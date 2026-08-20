#!/usr/bin/env python3
"""Report-only proof-module growth ratchet.

README.md:417-425 records the evidence behind both constants: a 1,244-line
model answered in about 21 seconds, while an 8,000-line derivation did not
answer inside the client's inactivity window.  Ordinary mode never writes.
``--write-baseline`` accepts new modules and ratchets decreases, but it never
raises an existing ceiling.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple


WARNING_THRESHOLD = 1250
NEW_MODULE_HARD_CAP = 8000
THRESHOLD_SOURCE = "README.md:417-425"
SCHEMA_VERSION = 1
BASELINE_REL = Path("scripts/proof-module-size-baseline.json")
EXCEPTIONS_REL = Path("scripts/proof-module-size-exceptions.json")
MODULE_RE = re.compile(r"Blanc/[A-Za-z_][A-Za-z0-9_]*\.lean\Z")
ID_RE = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*\Z")
OWNER_RE = ID_RE
FINDING_KINDS = {
    "warning-threshold",
    "grandfathered-growth",
    "new-module-hard-cap",
}


class ModuleSizeError(Exception):
    pass


@dataclass(frozen=True)
class Baseline:
    known_modules: Tuple[str, ...]
    ceilings: Dict[str, int]


@dataclass(frozen=True)
class ExceptionRow:
    id: str
    module: str
    finding: str
    allowed_lines: int
    rationale: str
    lsp_latency_ms: int
    lsp_evidence: str
    split_plan: str
    owner: str
    expires: datetime.date


@dataclass(frozen=True)
class Finding:
    module: str
    kind: str
    lines: int
    ceiling: Optional[int]


def strict_object(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    result: Dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ModuleSizeError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=strict_object)
    except ModuleSizeError:
        raise
    except (OSError, json.JSONDecodeError) as exc:
        raise ModuleSizeError(f"cannot read {path}: {exc}") from exc


def exact_keys(value: Any, expected: Set[str], where: str) -> Dict[str, Any]:
    if not isinstance(value, dict):
        raise ModuleSizeError(f"{where}: expected object")
    missing = expected - set(value)
    unknown = set(value) - expected
    if missing or unknown:
        raise ModuleSizeError(
            f"{where}: schema mismatch: missing {sorted(missing)}, unknown {sorted(unknown)}"
        )
    return value


def positive_int(value: Any, where: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ModuleSizeError(f"{where}: expected positive integer")
    return value


def module_path(value: Any, where: str) -> str:
    if not isinstance(value, str) or not MODULE_RE.fullmatch(value):
        raise ModuleSizeError(
            f"{where}: expected one concrete Blanc/*.lean module; wildcards and file-wide selectors are forbidden"
        )
    return value


def nonempty(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value.strip() or value != value.strip():
        raise ModuleSizeError(f"{where}: expected nonempty trimmed string")
    return value


def production_modules(root: Path) -> Dict[str, int]:
    source = root / "Blanc"
    if not source.is_dir():
        raise ModuleSizeError(f"production source directory not found: {source}")
    result: Dict[str, int] = {}
    for path in sorted(source.glob("*.lean")):
        try:
            lines = len(path.read_text(encoding="utf-8").splitlines())
        except OSError as exc:
            raise ModuleSizeError(f"cannot read {path}: {exc}") from exc
        result[path.relative_to(root).as_posix()] = lines
    if not result:
        raise ModuleSizeError(f"no production Blanc/*.lean modules found under {root}")
    return result


def empty_baseline() -> Baseline:
    return Baseline((), {})


def load_baseline(root: Path, allow_missing: bool = False) -> Baseline:
    path = root / BASELINE_REL
    if allow_missing and not path.exists():
        return empty_baseline()
    raw = exact_keys(
        load_json(path),
        {
            "_comment",
            "schemaVersion",
            "warningThreshold",
            "newModuleHardCap",
            "thresholdSource",
            "knownModules",
            "ceilings",
        },
        BASELINE_REL.as_posix(),
    )
    if raw["schemaVersion"] != SCHEMA_VERSION:
        raise ModuleSizeError("baseline schemaVersion must be 1")
    if raw["warningThreshold"] != WARNING_THRESHOLD:
        raise ModuleSizeError(f"baseline warningThreshold must be {WARNING_THRESHOLD}")
    if raw["newModuleHardCap"] != NEW_MODULE_HARD_CAP:
        raise ModuleSizeError(f"baseline newModuleHardCap must be {NEW_MODULE_HARD_CAP}")
    if raw["thresholdSource"] != THRESHOLD_SOURCE:
        raise ModuleSizeError(f"baseline thresholdSource must be {THRESHOLD_SOURCE!r}")
    nonempty(raw["_comment"], "baseline._comment")
    known_raw = raw["knownModules"]
    if not isinstance(known_raw, list):
        raise ModuleSizeError("baseline.knownModules: expected array")
    known = tuple(module_path(value, "baseline.knownModules") for value in known_raw)
    if tuple(sorted(known)) != known or len(set(known)) != len(known):
        raise ModuleSizeError("baseline.knownModules must be sorted and unique")
    ceilings_raw = raw["ceilings"]
    if not isinstance(ceilings_raw, dict):
        raise ModuleSizeError("baseline.ceilings: expected object")
    ceilings: Dict[str, int] = {}
    for module, value in ceilings_raw.items():
        checked = module_path(module, "baseline.ceilings key")
        lines = positive_int(value, f"baseline.ceilings[{module!r}]")
        if lines < WARNING_THRESHOLD:
            raise ModuleSizeError(
                f"baseline.ceilings[{module!r}]: ceiling below warning threshold"
            )
        if checked not in known:
            raise ModuleSizeError(f"baseline ceiling {module!r} is absent from knownModules")
        ceilings[checked] = lines
    if list(ceilings) != sorted(ceilings):
        raise ModuleSizeError("baseline.ceilings keys must be sorted")
    return Baseline(known, ceilings)


def load_exceptions(root: Path) -> Tuple[ExceptionRow, ...]:
    raw = exact_keys(
        load_json(root / EXCEPTIONS_REL),
        {"_comment", "schemaVersion", "exceptions"},
        EXCEPTIONS_REL.as_posix(),
    )
    if raw["schemaVersion"] != SCHEMA_VERSION:
        raise ModuleSizeError("exceptions schemaVersion must be 1")
    nonempty(raw["_comment"], "exceptions._comment")
    rows = raw["exceptions"]
    if not isinstance(rows, list):
        raise ModuleSizeError("exceptions.exceptions: expected array")
    result: List[ExceptionRow] = []
    ids: Set[str] = set()
    scopes: Set[Tuple[str, str]] = set()
    expected = {
        "id",
        "module",
        "finding",
        "allowedLines",
        "rationale",
        "lspLatencyMs",
        "lspEvidence",
        "splitPlan",
        "owner",
        "expires",
    }
    today = datetime.date.today()
    for index, value in enumerate(rows, 1):
        where = f"exceptions[{index}]"
        row = exact_keys(value, expected, where)
        row_id = nonempty(row["id"], f"{where}.id")
        if not ID_RE.fullmatch(row_id) or row_id in ids:
            raise ModuleSizeError(f"{where}.id: expected unique lowercase kebab id")
        ids.add(row_id)
        module = module_path(row["module"], f"{where}.module")
        finding = nonempty(row["finding"], f"{where}.finding")
        if finding not in FINDING_KINDS:
            raise ModuleSizeError(f"{where}.finding: expected one of {sorted(FINDING_KINDS)}")
        scope = (module, finding)
        if scope in scopes:
            raise ModuleSizeError(f"{where}: duplicate exception scope {scope}")
        scopes.add(scope)
        allowed = positive_int(row["allowedLines"], f"{where}.allowedLines")
        if allowed < WARNING_THRESHOLD:
            raise ModuleSizeError(f"{where}.allowedLines: must be at least {WARNING_THRESHOLD}")
        latency = positive_int(row["lspLatencyMs"], f"{where}.lspLatencyMs")
        owner = nonempty(row["owner"], f"{where}.owner")
        if not OWNER_RE.fullmatch(owner):
            raise ModuleSizeError(f"{where}.owner: expected lowercase kebab owner")
        expires_text = nonempty(row["expires"], f"{where}.expires")
        try:
            expires = datetime.date.fromisoformat(expires_text)
        except ValueError as exc:
            raise ModuleSizeError(f"{where}.expires: expected YYYY-MM-DD") from exc
        if expires.isoformat() != expires_text:
            raise ModuleSizeError(f"{where}.expires: expected canonical YYYY-MM-DD")
        if expires < today:
            raise ModuleSizeError(f"{where}: expired on {expires_text}")
        result.append(
            ExceptionRow(
                row_id,
                module,
                finding,
                allowed,
                nonempty(row["rationale"], f"{where}.rationale"),
                latency,
                nonempty(row["lspEvidence"], f"{where}.lspEvidence"),
                nonempty(row["splitPlan"], f"{where}.splitPlan"),
                owner,
                expires,
            )
        )
    return tuple(result)


def inventory_findings(modules: Dict[str, int], baseline: Baseline) -> Tuple[List[Finding], List[Tuple[str, int, int]]]:
    known = set(baseline.known_modules)
    findings: List[Finding] = []
    improvements: List[Tuple[str, int, int]] = []
    for module, lines in modules.items():
        if module not in known:
            if lines > NEW_MODULE_HARD_CAP:
                findings.append(Finding(module, "new-module-hard-cap", lines, None))
            elif lines >= WARNING_THRESHOLD:
                findings.append(Finding(module, "warning-threshold", lines, None))
            continue
        ceiling = baseline.ceilings.get(module)
        if ceiling is None:
            if lines >= WARNING_THRESHOLD:
                findings.append(Finding(module, "warning-threshold", lines, None))
        elif lines > ceiling:
            findings.append(Finding(module, "grandfathered-growth", lines, ceiling))
        elif lines < ceiling:
            improvements.append((module, ceiling, lines))
    return findings, improvements


def validate_integrity(modules: Dict[str, int], baseline: Baseline, allow_stale: bool) -> None:
    if allow_stale:
        return
    stale_known = sorted(set(baseline.known_modules) - set(modules))
    stale_ceilings = sorted(set(baseline.ceilings) - set(modules))
    if stale_known or stale_ceilings:
        raise ModuleSizeError(
            f"stale baseline: missing known modules {stale_known}; missing ceiling modules {stale_ceilings}"
        )


def validate_exceptions(
    modules: Dict[str, int], findings: Sequence[Finding], exceptions: Sequence[ExceptionRow]
) -> Dict[Tuple[str, str], ExceptionRow]:
    active = {(finding.module, finding.kind): finding for finding in findings}
    result: Dict[Tuple[str, str], ExceptionRow] = {}
    for row in exceptions:
        if row.module not in modules:
            raise ModuleSizeError(f"orphan exception {row.id!r}: module {row.module} does not exist")
        key = (row.module, row.finding)
        finding = active.get(key)
        if finding is None:
            raise ModuleSizeError(f"orphan exception {row.id!r}: no matching live finding")
        if modules[row.module] > row.allowed_lines:
            raise ModuleSizeError(
                f"exception {row.id!r}: {modules[row.module]} lines exceed bounded allowance {row.allowed_lines}"
            )
        result[key] = row
    return result


def baseline_document(baseline: Baseline) -> str:
    data = {
        "_comment": (
            "Grandfathered proof-module ceilings. Threshold evidence: README.md:417-425. "
            "Regenerate only with scripts/check-proof-module-size.sh --write-baseline; "
            "the writer never raises an existing ceiling."
        ),
        "schemaVersion": SCHEMA_VERSION,
        "warningThreshold": WARNING_THRESHOLD,
        "newModuleHardCap": NEW_MODULE_HARD_CAP,
        "thresholdSource": THRESHOLD_SOURCE,
        "knownModules": list(baseline.known_modules),
        "ceilings": {key: baseline.ceilings[key] for key in sorted(baseline.ceilings)},
    }
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def monotone_update(modules: Dict[str, int], previous: Baseline) -> Baseline:
    ceilings: Dict[str, int] = {}
    for module, lines in modules.items():
        old = previous.ceilings.get(module)
        if old is not None:
            lowered = min(old, lines)
            if lowered >= WARNING_THRESHOLD:
                ceilings[module] = lowered
        elif lines >= WARNING_THRESHOLD:
            ceilings[module] = lines
    return Baseline(tuple(sorted(modules)), ceilings)


def write_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", newline="", dir=path.parent, prefix=f".{path.name}.", delete=False
    )
    temporary = Path(handle.name)
    try:
        with handle:
            handle.write(text)
        os.chmod(temporary, 0o644)
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def ordinary(root: Path) -> int:
    modules = production_modules(root)
    baseline = load_baseline(root)
    exceptions = load_exceptions(root)
    validate_integrity(modules, baseline, False)
    findings, improvements = inventory_findings(modules, baseline)
    applied = validate_exceptions(modules, findings, exceptions)
    hard = 0
    growth = 0
    warnings = 0
    for finding in findings:
        row = applied.get((finding.module, finding.kind))
        tag = "EXCEPTED" if row else "FINDING"
        detail = f"{finding.lines} lines"
        if finding.ceiling is not None:
            detail += f", ceiling {finding.ceiling}"
        if row:
            detail += f", exception {row.id} through {row.expires.isoformat()}"
        print(f"MODULE-SIZE — {tag} {finding.kind}: {finding.module}: {detail}")
        if finding.kind == "new-module-hard-cap":
            hard += 1
        elif finding.kind == "grandfathered-growth":
            growth += 1
        else:
            warnings += 1
    for module, old, new in improvements:
        print(
            f"MODULE-SIZE — IMPROVED: {module}: {old} -> {new} lines; "
            "ratchet with --write-baseline"
        )
    print(
        f"OK — proof module size (report-only): {len(modules)} modules; "
        f"{len(baseline.ceilings)} grandfathered ceilings; {warnings} warning(s), "
        f"{growth} growth finding(s), {hard} new-module hard-cap breach(es), "
        f"{len(improvements)} improvement(s); {len(applied)} exception(s) applied"
    )
    return 0


def write_baseline(root: Path) -> int:
    modules = production_modules(root)
    baseline_exists = (root / BASELINE_REL).exists()
    previous = load_baseline(root, allow_missing=True)
    if baseline_exists:
        validate_integrity(modules, previous, True)
        new_hard_cap = sorted(
            module
            for module, lines in modules.items()
            if module not in previous.known_modules and lines > NEW_MODULE_HARD_CAP
        )
        if new_hard_cap:
            raise ModuleSizeError(
                "writer refuses to grandfather new modules above the hard cap: "
                f"{new_hard_cap}"
            )
    updated = monotone_update(modules, previous)
    for module, old in previous.ceilings.items():
        if module in updated.ceilings and updated.ceilings[module] > old:
            raise ModuleSizeError(f"writer attempted to raise {module}: {old} -> {updated.ceilings[module]}")
    write_atomic(root / BASELINE_REL, baseline_document(updated))
    print(
        f"OK — proof module size baseline: {len(updated.known_modules)} known modules; "
        f"{len(updated.ceilings)} ceilings; monotone baseline written"
    )
    return 0


def exception_document(rows: Sequence[Dict[str, Any]]) -> str:
    return json.dumps(
        {
            "_comment": (
                "Bounded, module-scoped proof-size exceptions. Every row expires and carries "
                "LSP latency evidence plus a split plan; wildcards are forbidden."
            ),
            "schemaVersion": SCHEMA_VERSION,
            "exceptions": list(rows),
        },
        indent=2,
    ) + "\n"


def write_module(root: Path, name: str, lines: int) -> None:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("-- line\n" * lines, encoding="utf-8")


def self_test() -> int:
    controls = 0
    with tempfile.TemporaryDirectory(prefix="proof-module-size-") as directory:
        root = Path(directory)
        (root / "scripts").mkdir()
        write_module(root, "Blanc/Small.lean", 100)
        write_module(root, "Blanc/Large.lean", 1500)
        write_atomic(root / EXCEPTIONS_REL, exception_document([]))
        write_baseline(root)
        baseline = load_baseline(root)

        write_module(root, "Blanc/Large.lean", 1501)
        findings, _ = inventory_findings(production_modules(root), baseline)
        if not any(row.kind == "grandfathered-growth" for row in findings):
            raise ModuleSizeError("self-test: growth past a ceiling was not detected")
        controls += 1

        write_module(root, "Blanc/NewHuge.lean", 8001)
        findings, _ = inventory_findings(production_modules(root), baseline)
        if not any(row.module.endswith("NewHuge.lean") and row.kind == "new-module-hard-cap" for row in findings):
            raise ModuleSizeError("self-test: new-module hard-cap breach was not detected")
        controls += 1

        write_module(root, "Blanc/Large.lean", 1400)
        lowered = monotone_update(production_modules(root), baseline)
        if lowered.ceilings.get("Blanc/Large.lean") != 1400:
            raise ModuleSizeError("self-test: decrease did not ratchet the ceiling down")
        controls += 1

        write_module(root, "Blanc/Large.lean", 1700)
        not_raised = monotone_update(production_modules(root), baseline)
        if not_raised.ceilings.get("Blanc/Large.lean") != 1500:
            raise ModuleSizeError("self-test: monotone writer raised an existing ceiling")
        controls += 1

        future = (datetime.date.today() + datetime.timedelta(days=30)).isoformat()
        past = (datetime.date.today() - datetime.timedelta(days=1)).isoformat()
        valid_row = {
            "id": "large-growth",
            "module": "Blanc/Large.lean",
            "finding": "grandfathered-growth",
            "allowedLines": 1800,
            "rationale": "Temporary measured growth.",
            "lspLatencyMs": 21000,
            "lspEvidence": "Whole-file diagnostic request transcript.",
            "splitPlan": "Split declarations by proof responsibility before expiry.",
            "owner": "proof-infrastructure",
            "expires": future,
        }

        def rejected(label: str, rows: Sequence[Dict[str, Any]], expected: str) -> None:
            nonlocal controls
            write_atomic(root / EXCEPTIONS_REL, exception_document(rows))
            try:
                loaded = load_exceptions(root)
                current = production_modules(root)
                current_findings, _ = inventory_findings(current, baseline)
                validate_exceptions(current, current_findings, loaded)
            except ModuleSizeError as exc:
                if expected not in str(exc):
                    raise ModuleSizeError(
                        f"self-test {label}: expected {expected!r}, got {str(exc)!r}"
                    ) from exc
            else:
                raise ModuleSizeError(f"self-test {label}: invalid control passed")
            controls += 1

        expired = dict(valid_row)
        expired["expires"] = past
        rejected("expired", [expired], "expired")
        orphan = dict(valid_row)
        orphan["module"] = "Blanc/NoSuch.lean"
        rejected("orphan", [orphan], "orphan exception")
        wildcard = dict(valid_row)
        wildcard["module"] = "Blanc/*.lean"
        rejected("file-wide", [wildcard], "wildcards and file-wide selectors are forbidden")

        write_atomic(root / EXCEPTIONS_REL, exception_document([]))
        stale_doc = json.loads(baseline_document(baseline))
        stale_doc["knownModules"].append("Blanc/Stale.lean")
        stale_doc["knownModules"].sort()
        write_atomic(root / BASELINE_REL, json.dumps(stale_doc, indent=2) + "\n")
        try:
            validate_integrity(production_modules(root), load_baseline(root), False)
        except ModuleSizeError as exc:
            if "stale baseline" not in str(exc):
                raise
        else:
            raise ModuleSizeError("self-test: stale baseline passed")
        controls += 1
    if controls != 8:
        raise ModuleSizeError(f"self-test accounting: expected 8 controls, ran {controls}")
    print(
        "OK — proof module size self-test: 8/8 growth, hard-cap, monotonicity, "
        "exception, and integrity controls live"
    )
    return 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    mode = result.add_mutually_exclusive_group()
    mode.add_argument("--write-baseline", action="store_true")
    mode.add_argument("--self-test", action="store_true")
    return result


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parser().parse_args(argv)
    try:
        if args.self_test:
            return self_test()
        root = args.root.resolve()
        if args.write_baseline:
            return write_baseline(root)
        return ordinary(root)
    except ModuleSizeError as exc:
        print(f"REGRESSION — proof module size: {exc}")
        return 1
    except OSError as exc:
        print(f"REGRESSION — proof module size: filesystem failure: {exc}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
