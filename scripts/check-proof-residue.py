#!/usr/bin/env python3
"""Blocking whole-tree, shrink-only checks for registered proof residues."""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import json
import pathlib
import re
import sys
import tempfile
from dataclasses import dataclass

REGISTRY = pathlib.Path("scripts/proof-residue-registry.json")
BASELINE = pathlib.Path("scripts/proof-residue-baseline.json")
SCHEMA = 1


class GateError(RuntimeError):
    pass


@dataclass(frozen=True)
class Predicate:
    id: str
    description: str
    owner: str
    reopen: str
    boundary: str
    includes: tuple[str, ...]
    pattern: str


def digest_payload(value: dict) -> str:
    body = {k: v for k, v in value.items() if k != "digest"}
    raw = json.dumps(body, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(raw.encode()).hexdigest()


def load_registry(root: pathlib.Path) -> tuple[list[Predicate], str]:
    path = root / REGISTRY
    if not path.is_file():
        raise GateError(f"missing registry: {REGISTRY}")
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as e:
        raise GateError(f"malformed registry: {e}") from e
    if set(raw) != {"schema_version", "predicates"} or raw.get("schema_version") != SCHEMA or not isinstance(raw.get("predicates"), list):
        raise GateError("registry fields/schema/predicates list is invalid")
    seen: set[str] = set()
    out: list[Predicate] = []
    for i, item in enumerate(raw["predicates"]):
        if not isinstance(item, dict):
            raise GateError(f"predicate[{i}] is not a table")
        required = {"id", "description", "owner", "reopen", "boundary", "include", "pattern"}
        if set(item) != required:
            raise GateError(f"predicate[{i}] fields must be exactly {sorted(required)}")
        vals = {k: item[k] for k in required}
        if any(not isinstance(vals[k], str) or not vals[k].strip() for k in ("id", "description", "owner", "reopen", "boundary", "pattern")):
            raise GateError(f"predicate[{i}] has empty/non-string scalar field")
        ident = vals["id"]
        if ident in seen or not re.fullmatch(r"[a-z][a-z0-9-]*", ident):
            raise GateError(f"predicate[{i}] has duplicate/invalid id {ident!r}")
        seen.add(ident)
        includes = vals["include"]
        if isinstance(includes, str):
            includes = [includes]
        if not isinstance(includes, list) or not includes or any(not isinstance(g, str) or not g for g in includes):
            raise GateError(f"predicate {ident}: include must be a nonempty string list")
        for glob in includes:
            p = pathlib.PurePosixPath(glob)
            if p.is_absolute() or ".." in p.parts or not glob.startswith("Blanc/"):
                raise GateError(f"predicate {ident}: include glob outside root: {glob!r}")
        try:
            re.compile(vals["pattern"])
        except re.error as e:
            raise GateError(f"predicate {ident}: invalid regex: {e}") from e
        out.append(Predicate(ident, vals["description"], vals["owner"], vals["reopen"], vals["boundary"], tuple(includes), vals["pattern"]))
    if not out:
        raise GateError("registry contains no predicates")
    registry_sha = hashlib.sha256(path.read_bytes()).hexdigest()
    return out, registry_sha


def mask_comments_literals(text: str, source_name: str) -> str:
    out = list(text)
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("--", i):
            while i < n and text[i] != "\n": out[i] = " "; i += 1
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "; depth = 1; i += 2
        elif text[i] == '"':
            out[i] = " "; i += 1; closed = False
            while i < n:
                if text[i] == "\\":
                    out[i] = " "; i += 1
                    if i < n: out[i] = " "; i += 1
                elif text[i] == '"':
                    out[i] = " "; i += 1; closed = True; break
                else:
                    if text[i] != "\n": out[i] = " "
                    i += 1
            if not closed:
                raise GateError(f"unterminated string literal in {source_name}")
        else:
            i += 1
    if depth:
        raise GateError(f"unterminated nested comment in {source_name}")
    return "".join(out)


def files_for(root: pathlib.Path, pred: Predicate) -> list[pathlib.Path]:
    paths: set[pathlib.Path] = set()
    for glob in pred.includes:
        paths.update(root.glob(glob))
    root_real = root.resolve()
    files = []
    for p in sorted(paths):
        if not p.is_file():
            continue
        try:
            p.resolve().relative_to(root_real)
        except ValueError:
            raise GateError(f"predicate {pred.id}: resolved path escapes repository root: {p}")
        files.append(p)
    if not files:
        raise GateError(f"predicate {pred.id}: include globs matched zero files")
    return files


def inventory(root: pathlib.Path, predicates: list[Predicate]) -> tuple[dict[str, list[str]], int, int]:
    hits: dict[str, list[str]] = {}
    inspected = 0
    for pred in predicates:
        found: list[str] = []
        for path in files_for(root, pred):
            try:
                source = path.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as e:
                raise GateError(f"unreadable source {path}: {e}") from e
            inspected += 1
            masked = mask_comments_literals(source, path.relative_to(root).as_posix())
            try:
                matches = list(re.finditer(pred.pattern, masked))
            except re.error as e:
                raise GateError(f"predicate {pred.id}: invalid regex: {e}") from e
            for match in matches:
                line = masked.count("\n", 0, match.start()) + 1
                found.append(f"{path.relative_to(root).as_posix()}:{line}")
        hits[pred.id] = found
    if inspected == 0:
        raise GateError("anti-vacuity: inspected zero files")
    return hits, inspected, sum(len(v) for v in hits.values())


def load_baseline(root: pathlib.Path) -> dict:
    path = root / BASELINE
    if not path.is_file():
        raise GateError(f"missing baseline: {BASELINE}")
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as e:
        raise GateError(f"malformed baseline: {e}") from e
    required = {"_comment", "schema_version", "registry_sha256", "predicates", "total", "digest"}
    if set(raw) != required or raw.get("schema_version") != SCHEMA:
        raise GateError("baseline fields/schema mismatch")
    if raw.get("digest") != digest_payload(raw):
        raise GateError("baseline digest mismatch")
    if not isinstance(raw["predicates"], dict) or any(type(v) is not int or v < 0 for v in raw["predicates"].values()):
        raise GateError("baseline predicate counts are invalid")
    if raw["total"] != sum(raw["predicates"].values()):
        raise GateError("baseline total disagrees with predicate counts")
    return raw


def baseline_document(registry_sha: str, counts: dict[str, int]) -> dict:
    doc = {"_comment": "Shrink-only proof-residue baseline; generated by check-proof-residue.sh --write-baseline.", "schema_version": SCHEMA, "registry_sha256": registry_sha, "predicates": dict(sorted(counts.items())), "total": sum(counts.values())}
    doc["digest"] = digest_payload(doc)
    return doc


def write_baseline(root: pathlib.Path, predicates: list[Predicate], registry_sha: str, hits: dict[str, list[str]], quiet: bool = False) -> int:
    counts = {p.id: len(hits[p.id]) for p in predicates}
    path = root / BASELINE
    old = load_baseline(root) if path.exists() else None
    if old:
        old_counts = old["predicates"]
        missing = set(old_counts) - set(counts)
        if missing: raise GateError(f"writer refuses predicate removal: {sorted(missing)}")
        rises = {k: (old_counts[k], v) for k, v in counts.items() if k in old_counts and v > old_counts[k]}
        if rises: raise GateError(f"writer refuses count rise: {rises}")
        new_nonzero = {k: v for k, v in counts.items() if k not in old_counts and v != 0}
        if new_nonzero: raise GateError(f"writer refuses nonzero new predicate admission: {new_nonzero}")
        changed = old.get("registry_sha256") != registry_sha
        if changed and not quiet:
            print("NOTICE — residue baseline: existing predicate pattern/digest changed under explicit shrink-only write")
    doc = baseline_document(registry_sha, counts)
    (root / BASELINE).write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    if not quiet:
        print(f"OK — proof residue baseline: {len(counts)} predicates, {doc['total']} hits; shrink-only baseline written")
    return 0


def run(root: pathlib.Path, write: bool = False) -> int:
    predicates, registry_sha = load_registry(root)
    hits, inspected, total = inventory(root, predicates)
    print(f"residue scan: {inspected} source file(s), {len(predicates)} predicate(s), {total} hit(s)")
    for pred in predicates:
        print(f"  {pred.id}: {len(hits[pred.id])} hit(s)")
        for hit in hits[pred.id]: print(f"    HIT {hit}")
    if write: return write_baseline(root, predicates, registry_sha, hits)
    base = load_baseline(root)
    if base["registry_sha256"] != registry_sha: raise GateError("baseline registry/digest mismatch")
    if set(base["predicates"]) != {p.id for p in predicates}: raise GateError("baseline predicate membership mismatch")
    rises = {p.id: (base["predicates"][p.id], len(hits[p.id])) for p in predicates if len(hits[p.id]) > base["predicates"][p.id]}
    if total > base["total"] or rises: raise GateError(f"residue count rise: {rises or {'total': (base['total'], total)}}")
    print(f"OK — proof residue: {len(predicates)}/{len(predicates)} predicates checked; counts {base['total']} -> {total}; no rise")
    return 0


def self_test() -> int:
    def silent_run(root: pathlib.Path) -> int:
        with contextlib.redirect_stdout(io.StringIO()):
            return run(root)

    def predicate(ident: str, pattern: str, include=None) -> dict:
        return {
            "id": ident,
            "description": f"{ident} fixture",
            "owner": "self-test",
            "reopen": "seed",
            "boundary": "self-test text",
            "include": include or ["Blanc/*.lean"],
            "pattern": pattern,
        }

    def write_registry(root: pathlib.Path, predicates: list[dict]) -> None:
        (root / REGISTRY).write_text(json.dumps({
            "schema_version": SCHEMA,
            "predicates": predicates,
        }, indent=2) + "\n", encoding="utf-8")

    with tempfile.TemporaryDirectory(prefix="proof-residue-") as d:
        root = pathlib.Path(d); (root / "Blanc").mkdir(); (root / "scripts").mkdir()
        clean = "theorem clean : True := by\n  trivial\n"
        (root / "Blanc" / "Fixture.lean").write_text(clean, encoding="utf-8")
        base_predicates = [predicate("fixture", r"forbidden\b")]
        write_registry(root, base_predicates)
        preds, sha = load_registry(root); hits, _, _ = inventory(root, preds); write_baseline(root, preds, sha, hits, quiet=True); silent_run(root)
        (root / "Blanc" / "Fixture.lean").write_text("theorem clean : True := by\n  forbidden\n", encoding="utf-8")
        try: silent_run(root)
        except GateError as e:
            if "rise" not in str(e): raise
        else: raise GateError("self-test seeded rise did not block")
        (root / "Blanc" / "Fixture.lean").write_text(clean, encoding="utf-8"); silent_run(root)
        (root / REGISTRY).write_text("{not valid", encoding="utf-8")
        try: load_registry(root)
        except GateError: pass
        else: raise GateError("self-test malformed registry passed")
        write_registry(root, base_predicates)
        baseline = load_baseline(root); baseline["digest"] = "0"; (root / BASELINE).write_text(json.dumps(baseline))
        try: load_baseline(root)
        except GateError: pass
        else: raise GateError("self-test digest drift passed")
        (root / BASELINE).unlink()
        # Lexer and structural controls.
        for bad_source, needle in (("/- unterminated", "unterminated nested comment"), ("\"unterminated", "unterminated string literal")):
            try: mask_comments_literals(bad_source, "Blanc/Fixture.lean")
            except GateError as e:
                if needle not in str(e): raise
            else: raise GateError("self-test unterminated lexical state passed")
        selector_re = re.compile(r"(?m)^\s*(?:·\s*)?rw\s+\[hselector\]\s*$\n\s*(?:·\s*)?decide\s+\+kernel\b")
        if len(selector_re.findall("· rw [hselector]\n  decide +kernel\n")) != 1:
            raise GateError("self-test optional selector bullet did not match")
        if selector_re.search("· rw [hselector]\n  decide +kernel\n\ntheorem later : True := by\n  rfl\n") is None:
            raise GateError("self-test live selector-shaped match did not match")
        bounded = re.compile(r"(?ms)^theorem named\b(?:(?!^(?:private\s+)?(?:theorem|lemma|def)\b).)*?^\s*rfl\s*$")
        crossed = bounded.search("theorem named : True := by\n  exact True.intro\n\ntheorem later : True := by\n  rfl\n")
        if crossed is not None:
            raise GateError("self-test bounded predicate crossed a declaration")
        # A query which matches no files is never a vacuous green.
        write_registry(root, [predicate("fixture", r"forbidden\b", ["Blanc/Missing*.lean"])])
        try: inventory(root, load_registry(root)[0])
        except GateError as e:
            if "zero files" not in str(e): raise
        else: raise GateError("self-test zero-file query passed")
        # Writer controls: an existing rise is refused, while a new zero-count
        # predicate is admitted only through the explicit writer.
        write_registry(root, base_predicates)
        preds, sha = load_registry(root); hits, _, _ = inventory(root, preds)
        write_baseline(root, preds, sha, hits, quiet=True)
        hits["fixture"] = ["Blanc/Fixture.lean:1"]
        try: write_baseline(root, preds, sha, hits)
        except GateError as e:
            if "count rise" not in str(e): raise
        else: raise GateError("self-test writer rise passed")
        write_registry(root, base_predicates + [predicate("new-zero", r"^\s*never_matches\b")])
        preds, sha = load_registry(root); hits, _, _ = inventory(root, preds); write_baseline(root, preds, sha, hits, quiet=True)
        # A new nonzero predicate is debt admission, not a shrink-only refresh.
        write_registry(root, base_predicates + [
            predicate("new-zero", r"^\s*never_matches\b"),
            predicate("new-live", r"^theorem\s+clean\b"),
        ])
        preds, sha = load_registry(root); hits, _, _ = inventory(root, preds)
        try: write_baseline(root, preds, sha, hits, quiet=True)
        except GateError as e:
            if "nonzero new predicate" not in str(e): raise
        else: raise GateError("self-test nonzero new predicate admission passed")
        # Resolving a registered path through a symlink may not escape root.
        outside = pathlib.Path(d).parent / f"{root.name}-outside.lean"
        try:
            outside.write_text(clean, encoding="utf-8")
            link = root / "Blanc" / "Escape.lean"
            link.symlink_to(outside)
            escape = predicate("escape", r"clean", ["Blanc/Escape.lean"])
            try: files_for(root, Predicate(
                escape["id"], escape["description"], escape["owner"],
                escape["reopen"], escape["boundary"],
                tuple(escape["include"]), escape["pattern"],
            ))
            except GateError as e:
                if "escapes repository root" not in str(e): raise
            else: raise GateError("self-test escaping symlink passed")
        finally:
            outside.unlink(missing_ok=True)
    print("OK — proof residue self-test: 15 green/seed/lexical/query/path/digest/writer controls live")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(); ap.add_argument("--root", type=pathlib.Path, default=pathlib.Path(__file__).resolve().parent.parent); ap.add_argument("--write-baseline", action="store_true"); ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    try:
        if args.self_test: return self_test()
        root = args.root.resolve(); return run(root, args.write_baseline)
    except GateError as e:
        print(f"REGRESSION — proof residue: {e}")
        return 1


if __name__ == "__main__": sys.exit(main())
