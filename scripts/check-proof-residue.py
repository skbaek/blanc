#!/usr/bin/env python3
"""Blocking whole-tree, shrink-only checks for registered proof residues.

Ordinary --write-baseline still refuses predicate removal. Explicit retirement
additionally requires --retire-predicate ID (repeatable), --previous-registry
PATH and --expected-baseline-sha256 SHA. It verifies the old registry/baseline
binding, absent old subjects and unchanged surviving patterns/populations before
using the same shrink-only writer. Retirement cannot admit new predicates.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import json
import pathlib
import re
import stat
import sys
import tempfile
from dataclasses import dataclass

REGISTRY = pathlib.Path("scripts/proof-residue-registry.json")
BASELINE = pathlib.Path("scripts/proof-residue-baseline.json")
SCHEMA = 1


class GateError(RuntimeError):
    pass


class NoPredicateFiles(GateError):
    """Only the exact empty-population refusal, never a filesystem failure."""


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
    return load_registry_file(root / REGISTRY)


def load_registry_file(path: pathlib.Path) -> tuple[list[Predicate], str]:
    if not path.is_file():
        raise GateError(f"missing registry: {REGISTRY}")
    try:
        data = path.read_bytes()
        raw = json.loads(data.decode("utf-8"))
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
    registry_sha = hashlib.sha256(data).hexdigest()
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
        raise NoPredicateFiles(f"predicate {pred.id}: include globs matched zero files")
    return files


def _migration_file_bytes(path: pathlib.Path, label: str) -> bytes:
    # Canonicalize the parent (including the platform's temporary directory),
    # but require the file itself to have its exact, unaliased directory entry.
    parent = path.parent.resolve(strict=True)
    if path.name not in {entry.name for entry in parent.iterdir()}:
        raise GateError(f"retirement {label}: missing exact file entry")
    path = parent / path.name
    info = path.lstat()
    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
        raise GateError(f"retirement {label}: file alias or non-regular file")
    return path.read_bytes()


def _migration_source_aliases(root: pathlib.Path) -> None:
    # Path.glob may skip a dangling link or a linked directory. Such a skip
    # cannot establish that a retired subject is absent. Do not follow links.
    if (root / "scripts").is_symlink():
        raise GateError("retirement scripts directory alias")
    pending = [root / "Blanc"]
    while pending:
        path = pending.pop()
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise GateError(f"retirement source alias: {path.relative_to(root)}")
        if stat.S_ISDIR(info.st_mode):
            pending.extend(path.iterdir())
        elif path.suffix == ".lean" and (
            not stat.S_ISREG(info.st_mode) or info.st_nlink != 1
        ):
            raise GateError(f"retirement source alias: {path.relative_to(root)}")


def _migration_population(root: pathlib.Path, pred: Predicate) -> set[pathlib.Path]:
    try:
        return set(files_for(root, pred))
    except NoPredicateFiles:
        return set()


def validate_retirement(
    root: pathlib.Path, predicates: list[Predicate], registry_sha: str,
    old: dict | None, retired: tuple[str, ...],
    previous_registry: pathlib.Path | None, expected_baseline_sha256: str | None,
    admit_new: tuple[str, ...],
) -> set[str]:
    """Verify a writer-only, exact absent-subject migration; write nothing."""
    if not retired or previous_registry is None or expected_baseline_sha256 is None:
        raise GateError("retirement requires exact IDs, previous registry and baseline SHA-256")
    if admit_new:
        raise GateError("retirement cannot be mixed with new predicate admission")
    if len(retired) != len(set(retired)):
        raise GateError("retirement refuses duplicate predicate ID")
    if old is None:
        raise GateError("retirement requires an existing validated baseline")
    if not re.fullmatch(r"[0-9a-f]{64}", expected_baseline_sha256):
        raise GateError("retirement baseline SHA-256 must be 64 lowercase hex digits")
    try:
        _migration_source_aliases(root)
        baseline_bytes = _migration_file_bytes(root / BASELINE, "baseline")
        if hashlib.sha256(baseline_bytes).hexdigest() != expected_baseline_sha256:
            raise GateError("retirement baseline SHA-256 mismatch")
        if json.loads(baseline_bytes) != old:
            raise GateError("retirement baseline changed during validation")
        current_bytes = _migration_file_bytes(root / REGISTRY, "current registry")
        current, current_sha = load_registry(root)
        if (hashlib.sha256(current_bytes).hexdigest() != registry_sha or
                current_sha != registry_sha or current != predicates):
            raise GateError("retirement current registry changed during validation")
        previous_bytes = _migration_file_bytes(previous_registry, "previous registry")
        if hashlib.sha256(previous_bytes).hexdigest() != old["registry_sha256"]:
            raise GateError("retirement previous registry/baseline hash mismatch")
        previous, previous_sha = load_registry_file(previous_registry)
        if previous_sha != old["registry_sha256"]:
            raise GateError("retirement previous registry changed during validation")
        old_by_id = {pred.id: pred for pred in previous}
        new_by_id = {pred.id: pred for pred in predicates}
        if set(old_by_id) != set(old["predicates"]):
            raise GateError("retirement previous registry/baseline membership mismatch")
        if set(new_by_id) - set(old_by_id):
            raise GateError("retirement cannot add new predicates")
        missing = set(old_by_id) - set(new_by_id)
        if set(retired) != missing:
            raise GateError("retirement IDs must exactly equal removed predicates: "
                            f"expected {sorted(missing)}, got {sorted(set(retired))}")
        for ident in sorted(missing):
            if _migration_population(root, old_by_id[ident]):
                raise GateError(f"retirement subject population still live: {ident}")
        for ident, pred in new_by_id.items():
            previous_pred = old_by_id[ident]
            if pred.pattern != previous_pred.pattern:
                raise GateError(f"retirement surviving pattern changed: {ident}")
            if _migration_population(root, previous_pred) != set(files_for(root, pred)):
                raise GateError(f"retirement surviving population changed: {ident}")
        return missing
    except OSError as exc:
        raise GateError(f"retirement filesystem query failed: {exc}") from exc


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


def write_baseline(
    root: pathlib.Path,
    predicates: list[Predicate],
    registry_sha: str,
    hits: dict[str, list[str]],
    quiet: bool = False,
    admit_new: tuple[str, ...] = (),
    retire: tuple[str, ...] = (),
    previous_registry: pathlib.Path | None = None,
    expected_baseline_sha256: str | None = None,
) -> int:
    counts = {p.id: len(hits[p.id]) for p in predicates}
    path = root / BASELINE
    old = load_baseline(root) if path.exists() else None
    migration = bool(retire or previous_registry is not None or expected_baseline_sha256 is not None)
    removed = validate_retirement(
        root, predicates, registry_sha, old, retire, previous_registry,
        expected_baseline_sha256, admit_new,
    ) if migration else set()
    if len(admit_new) != len(set(admit_new)):
        raise GateError(f"writer refuses duplicate admission id: {list(admit_new)}")
    admitted = set(admit_new)
    if old:
        old_counts = old["predicates"]
        missing = set(old_counts) - set(counts)
        if missing - removed: raise GateError(f"writer refuses predicate removal: {sorted(missing)}")
        rises = {k: (old_counts[k], v) for k, v in counts.items() if k in old_counts and v > old_counts[k]}
        if rises: raise GateError(f"writer refuses count rise: {rises}")
        unknown = admitted - set(counts)
        if unknown: raise GateError(f"writer refuses unknown admission id: {sorted(unknown)}")
        existing = admitted & set(old_counts)
        if existing: raise GateError(f"writer refuses existing predicate admission: {sorted(existing)}")
        new_nonzero = {k: v for k, v in counts.items() if k not in old_counts and v != 0}
        non_nonzero = admitted - set(new_nonzero)
        if non_nonzero:
            raise GateError(
                "writer refuses zero-count/non-nonzero admission id: "
                f"{sorted(non_nonzero)}"
            )
        unnamed = {k: v for k, v in new_nonzero.items() if k not in admitted}
        if unnamed: raise GateError(f"writer refuses unnamed nonzero new predicate admission: {unnamed}")
        changed = old.get("registry_sha256") != registry_sha
        if changed and not quiet:
            print("NOTICE — residue baseline: existing predicate pattern/digest changed under explicit shrink-only write")
        if admitted and not quiet:
            observed = {k: counts[k] for k in sorted(admitted)}
            print(f"NOTICE — residue baseline: exact new predicate admission: {observed}")
    elif admitted:
        raise GateError("writer refuses new predicate admission without an existing baseline")
    if removed and not quiet:
        print(f"NOTICE — residue retirement: absent-subject predicates {sorted(removed)}; "
              f"old baseline SHA-256 {expected_baseline_sha256}")
    doc = baseline_document(registry_sha, counts)
    (root / BASELINE).write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    if not quiet:
        print(f"OK — proof residue baseline: {len(counts)} predicates, {doc['total']} hits; shrink-only baseline written")
    return 0


def run(
    root: pathlib.Path, write: bool = False, admit_new: tuple[str, ...] = (),
    retire: tuple[str, ...] = (), previous_registry: pathlib.Path | None = None,
    expected_baseline_sha256: str | None = None,
) -> int:
    if (retire or previous_registry is not None or expected_baseline_sha256 is not None) and not write:
        raise GateError("retirement options are illegal without --write-baseline")
    if admit_new and not write:
        raise GateError("--admit-new is illegal without --write-baseline")
    predicates, registry_sha = load_registry(root)
    hits, inspected, total = inventory(root, predicates)
    print(f"residue scan: {inspected} source file(s), {len(predicates)} predicate(s), {total} hit(s)")
    for pred in predicates:
        print(f"  {pred.id}: {len(hits[pred.id])} hit(s)")
        for hit in hits[pred.id]: print(f"    HIT {hit}")
    if write:
        return write_baseline(
            root, predicates, registry_sha, hits, admit_new=admit_new,
            retire=retire, previous_registry=previous_registry,
            expected_baseline_sha256=expected_baseline_sha256,
        )
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
        write_registry(root, base_predicates + [
            predicate("new-zero", r"^\s*never_matches\b"),
            predicate("admit-zero", r"^\s*also_never_matches\b"),
        ])
        zero_preds, zero_sha = load_registry(root)
        zero_hits, _, _ = inventory(root, zero_preds)
        try:
            write_baseline(
                root, zero_preds, zero_sha, zero_hits, quiet=True,
                admit_new=("admit-zero",),
            )
        except GateError as e:
            if "zero-count/non-nonzero admission id" not in str(e): raise
        else: raise GateError("self-test named zero-count admission passed")
        # A new nonzero predicate is debt admission, not a shrink-only refresh.
        write_registry(root, base_predicates + [
            predicate("new-zero", r"^\s*never_matches\b"),
            predicate("new-live", r"^theorem\s+clean\b"),
        ])
        preds, sha = load_registry(root); hits, _, _ = inventory(root, preds)
        try: write_baseline(root, preds, sha, hits, quiet=True)
        except GateError as e:
            if "unnamed nonzero new predicate" not in str(e): raise
        else: raise GateError("self-test nonzero new predicate admission passed")
        # The writer may admit exactly the observed count of an explicitly
        # named new registry predicate.
        write_baseline(
            root, preds, sha, hits, quiet=True, admit_new=("new-live",),
        )
        admitted_baseline = load_baseline(root)
        if admitted_baseline["predicates"].get("new-live") != 1:
            raise GateError("self-test exact new predicate admission count drifted")
        # Admission IDs must be unique, registered, and absent from the old
        # baseline.  The option is writer-only.
        try: run(root, admit_new=("new-live",))
        except GateError as e:
            if "illegal without --write-baseline" not in str(e): raise
        else: raise GateError("self-test reader admission passed")
        for bad_ids, needle in (
            (("missing",), "unknown admission id"),
            (("new-live", "new-live"), "duplicate admission id"),
            (("fixture",), "existing predicate admission"),
        ):
            try:
                write_baseline(
                    root, preds, sha, hits, quiet=True, admit_new=bad_ids,
                )
            except GateError as e:
                if needle not in str(e): raise
            else: raise GateError("self-test invalid admission id passed")
        write_registry(root, [
            predicate("new-zero", r"^\s*never_matches\b"),
            predicate("new-live", r"^theorem\s+clean\b"),
        ])
        reduced_preds, reduced_sha = load_registry(root)
        reduced_hits, _, _ = inventory(root, reduced_preds)
        try:
            write_baseline(
                root, reduced_preds, reduced_sha, reduced_hits, quiet=True,
                admit_new=("fixture",),
            )
        except GateError as e:
            if "predicate removal" not in str(e): raise
        else: raise GateError("self-test named predicate removal passed")
        write_registry(root, base_predicates + [
            predicate("new-zero", r"^\s*never_matches\b"),
            predicate("new-live", r"^theorem\s+clean\b"),
        ])
        # Naming an existing predicate cannot waive the shrink-only count
        # rule: the rise is rejected before existing-ID validation.
        hits["fixture"] = ["Blanc/Fixture.lean:1"]
        try:
            write_baseline(
                root, preds, sha, hits, quiet=True, admit_new=("fixture",),
            )
        except GateError as e:
            if "count rise" not in str(e): raise
        else: raise GateError("self-test named existing rise passed")
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
    retirement_controls = retirement_self_test()
    print("OK — proof residue self-test: 20 existing green/seed/lexical/query/path/digest/writer/admission "
          f"and {retirement_controls} retirement controls live")
    return 0


def retirement_self_test() -> int:
    """Small absent-subject fixtures exercise the real writer and no-write refusals."""
    controls = 0
    rejected_cases = [
        ("ordinary-write", "writer refuses predicate removal"),
        ("ordinary-read", "registry/digest mismatch"),
        ("wrong-baseline-hash", "baseline SHA-256 mismatch"),
        ("wrong-registry-hash", "previous registry/baseline hash mismatch"),
        ("missing-registry", "missing exact file entry"),
        ("missing-hash", "requires exact IDs"),
        ("missing-id", "requires exact IDs"),
        ("incomplete-id-set", "IDs must exactly equal"),
        ("missing-baseline", "requires an existing validated baseline"),
        ("extra-id", "IDs must exactly equal"),
        ("duplicate-id", "duplicate predicate ID"),
        ("still-live-zero-hit-subject", "subject population still live"),
        ("survivor-pattern", "surviving pattern changed"),
        ("survivor-population", "surviving population changed"),
        ("mixed-new-zero-predicate", "cannot add new predicates"),
        ("mixed-admission", "cannot be mixed with new predicate admission"),
        ("survivor-rise", "writer refuses count rise"),
        ("empty-registry", "registry contains no predicates"),
        ("malformed-registry", "malformed registry"),
        ("previous-registry-alias", "file alias or non-regular"),
        ("dangling-subject-alias", "source alias"),
        ("source-directory-alias", "source alias"),
        ("source-hardlink", "source alias"),
        ("filesystem-error", "filesystem query failed"),
    ]
    for label, expected in [("authorized", "")] + rejected_cases:
        with tempfile.TemporaryDirectory(prefix="residue-retirement-") as directory:
            root = pathlib.Path(directory)
            (root / "Blanc").mkdir(); (root / "scripts").mkdir()
            keep = root / "Blanc" / "Keep.lean"
            subject = root / "Blanc" / "Retired.lean"
            keep.write_text("theorem keep : True := by\n  forbidden\n", encoding="utf-8")
            subject.write_text("theorem old : True := by\n  forbidden\n", encoding="utf-8")
            def row(ident: str, include: str) -> dict:
                return {"id": ident, "description": "retirement fixture",
                        "owner": "self-test", "reopen": "seed", "boundary": "text",
                        "include": [include], "pattern": r"forbidden\b"}
            old_rows = [row("live", "Blanc/Keep*.lean"), row("retired", "Blanc/Retired.lean")]
            if label == "incomplete-id-set":
                old_rows.append(row("retired-extra", "Blanc/RetiredExtra.lean"))
                (root / "Blanc" / "RetiredExtra.lean").write_text("forbidden\n", encoding="utf-8")
            def registry(rows: list[dict]) -> None:
                (root / REGISTRY).write_text(json.dumps({"schema_version": SCHEMA,
                                                       "predicates": rows}, indent=2) + "\n",
                                             encoding="utf-8")
            registry(old_rows)
            previous = root / "previous-registry.json"
            previous.write_bytes((root / REGISTRY).read_bytes())
            old_preds, old_sha = load_registry(root)
            old_hits, _, _ = inventory(root, old_preds)
            write_baseline(root, old_preds, old_sha, old_hits, quiet=True)
            baseline_before = (root / BASELINE).read_bytes()
            old_baseline_sha = hashlib.sha256(baseline_before).hexdigest()
            subject.unlink()
            if label == "incomplete-id-set":
                (root / "Blanc" / "RetiredExtra.lean").unlink()
            live_rows = [dict(old_rows[0])]
            registry(live_rows)
            kwargs = {"write": True, "retire": ("retired",),
                      "previous_registry": previous,
                      "expected_baseline_sha256": old_baseline_sha}
            if label == "ordinary-write":
                kwargs = {"write": True}
            elif label == "ordinary-read":
                kwargs = {}
            elif label == "wrong-baseline-hash":
                kwargs["expected_baseline_sha256"] = "0" * 64
            elif label == "wrong-registry-hash":
                previous.write_bytes(previous.read_bytes() + b"\n")
            elif label == "missing-registry":
                previous.unlink()
            elif label == "missing-hash":
                kwargs["expected_baseline_sha256"] = None
            elif label == "missing-id":
                kwargs["retire"] = ()
            elif label == "missing-baseline":
                (root / BASELINE).unlink()
                baseline_before = None
            elif label == "extra-id":
                kwargs["retire"] = ("retired", "unknown")
            elif label == "duplicate-id":
                kwargs["retire"] = ("retired", "retired")
            elif label == "still-live-zero-hit-subject":
                subject.write_text("theorem old : True := by\n  trivial\n", encoding="utf-8")
            elif label == "survivor-pattern":
                live_rows[0]["pattern"] = r"never_matches\b"; registry(live_rows)
            elif label == "survivor-population":
                (root / "Blanc" / "KeepExtra.lean").write_text("-- no hit\n", encoding="utf-8")
                live_rows[0]["include"] = ["Blanc/Keep.lean"]; registry(live_rows)
            elif label == "mixed-new-zero-predicate":
                new = row("new-zero", "Blanc/Keep.lean"); new["pattern"] = r"never_matches\b"
                registry(live_rows + [new])
            elif label == "mixed-admission":
                kwargs["admit_new"] = ("new",)
            elif label == "survivor-rise":
                keep.write_text("forbidden forbidden\n", encoding="utf-8")
            elif label == "empty-registry":
                registry([])
            elif label == "malformed-registry":
                (root / REGISTRY).write_text("{bad", encoding="utf-8")
            elif label == "previous-registry-alias":
                alias = root / "previous-alias.json"; alias.symlink_to(previous)
                kwargs["previous_registry"] = alias
            elif label == "dangling-subject-alias":
                subject.symlink_to(root / "absent.lean")
            elif label == "source-directory-alias":
                actual = root / "actual-source"; (root / "Blanc").rename(actual)
                (root / "Blanc").symlink_to(actual, target_is_directory=True)
            elif label == "source-hardlink":
                (root / "Blanc" / "KeepAlias.lean").hardlink_to(keep)
            original_files_for = files_for
            if label == "filesystem-error":
                def query_error(query_root: pathlib.Path, pred: Predicate) -> list[pathlib.Path]:
                    if pred.id == "retired":
                        raise OSError("retired population fixture query error")
                    return original_files_for(query_root, pred)
                globals()["files_for"] = query_error
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    run(root, **kwargs)
            except GateError as exc:
                if label == "authorized" or expected not in str(exc):
                    raise GateError(f"retirement self-test {label}: wrong refusal: {exc}") from exc
                if ((baseline_before is None and (root / BASELINE).exists()) or
                        (baseline_before is not None and (root / BASELINE).read_bytes() != baseline_before)):
                    raise GateError(f"retirement self-test {label}: rejected request wrote baseline")
                print(f"CONTROL — residue retirement {label}: {exc}; baseline unchanged")
            else:
                if label != "authorized":
                    raise GateError(f"retirement self-test {label}: invalid retirement passed")
                after = load_baseline(root)
                _, current_sha = load_registry(root)
                if (after["predicates"] != {"live": 1} or after["total"] != 1 or
                        after["registry_sha256"] != current_sha or
                        (root / BASELINE).read_text(encoding="utf-8") !=
                        json.dumps(baseline_document(current_sha, {"live": 1}), indent=2) + "\n"):
                    raise GateError("retirement self-test authorized: registered output differs")
                with contextlib.redirect_stdout(io.StringIO()):
                    run(root)
                print("CONTROL — residue retirement authorized: exact registered output and ordinary check green")
            finally:
                globals()["files_for"] = original_files_for
            controls += 1
    return controls


def main() -> int:
    ap = argparse.ArgumentParser(); ap.add_argument("--root", type=pathlib.Path, default=pathlib.Path(__file__).resolve().parent.parent); ap.add_argument("--write-baseline", action="store_true"); ap.add_argument("--admit-new", action="append", default=[], metavar="ID"); ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--retire-predicate", action="append", default=[], metavar="ID",
                    help="writer-only exact removed predicate ID; repeat for every retirement")
    ap.add_argument("--previous-registry", type=pathlib.Path, metavar="PATH",
                    help="writer-only previous registry bound by the validated old baseline")
    ap.add_argument("--expected-baseline-sha256", metavar="SHA",
                    help="writer-only SHA-256 of the exact old baseline bytes")
    args = ap.parse_args()
    try:
        retirement = bool(args.retire_predicate or args.previous_registry is not None or
                          args.expected_baseline_sha256 is not None)
        if retirement and (not args.write_baseline or args.self_test):
            raise GateError("retirement options require --write-baseline without --self-test")
        if args.admit_new and not args.write_baseline:
            raise GateError("--admit-new is illegal without --write-baseline")
        if args.self_test: return self_test()
        root = args.root.resolve()
        return run(root, args.write_baseline, tuple(args.admit_new),
                   tuple(args.retire_predicate), args.previous_registry,
                   args.expected_baseline_sha256)
    except GateError as e:
        print(f"REGRESSION — proof residue: {e}")
        return 1


if __name__ == "__main__": sys.exit(main())
