#!/usr/bin/env python3
"""Bounded evidence harness for the Lean-native statement-identity shadow pilot."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Callable

import gate_semaphore
import lean_native_identity_shadow as native
from lean_header import header_before_definition, parser_controls

ROOT = Path(__file__).resolve().parent.parent

ACTUAL = {
    "Blanc.LidoCircuitBreaker.assignmentPost_assignment": (
        "Blanc/LidoCircuitBreakerPreControl.lean", "assignmentPost_assignment",
        "37f3bb10eab7d8ec7fbbe82fa5dc3b0430e29f96f8443545108cd02740f70413"),
    "Blanc.LidoCircuitBreaker.pauseCall_boundary": (
        "Blanc/LidoCircuitBreakerCallBoundary.lean", "pauseCall_boundary",
        "5305fcec2a37665ade6f7b77d8edd2f493d8c65cb3a3f9f87ade7357d3a75499"),
    "Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSite?_sound": (
        "Blanc/LidoCircuitBreakerSites.lean", "RuntimePersistentWrite.sourceSite?_sound",
        "cff8ce690c1d300ce608e20e5303eaf6404079e433a75a7266a720e12b0c4ca1"),
    "Blanc.LidoCircuitBreaker.getPausables_runCompiled": (
        "Blanc/LidoCircuitBreakerEnumeration.lean", "getPausables_runCompiled",
        "860917a14bb01c38221ef7a97c5da4247aa3453b877183eb60d5f5cdde83f0d3"),
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run_shadow(scope: str, output: Path) -> dict[str, Any]:
    checker = ROOT / f"scripts/check-lido-circuit-breaker-{scope}.py"
    env = dict(os.environ)
    env.update({
        native.SHADOW_ENV: "1",
        native.OUTPUT_ENV: str(output),
        "BLANC_GATE_SEMAPHORE_WAIT": env.get("BLANC_GATE_SEMAPHORE_WAIT", "900"),
        "PYTHONPYCACHEPREFIX": env.get("PYTHONPYCACHEPREFIX", "/tmp/blanc-native-id-pyc"),
    })
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.perf_counter()
    run = subprocess.run(
        [sys.executable, str(checker), "--native-identity-shadow-only"],
        cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    if run.returncode:
        raise RuntimeError(f"{scope} shadow failed ({run.returncode}):\n{run.stdout}")
    expected = f"OK — S{'5' if scope == 'access' else '3'} native-identity shadow probe"
    if run.stdout.strip() != expected:
        raise RuntimeError(f"{scope} unexpected verdict: {run.stdout!r}")
    return {
        "command": f"python3 {checker.relative_to(ROOT)} --native-identity-shadow-only",
        "exit": run.returncode,
        "verdict": run.stdout.strip(),
        "wall_seconds": round(elapsed, 6),
        "child_user_seconds": round(after.ru_utime - before.ru_utime, 6),
        "child_system_seconds": round(after.ru_stime - before.ru_stime, 6),
        # ru_maxrss is a high-water mark for all children of this harness; retain
        # its scope explicitly rather than mislabelling it as isolated overhead.
        "child_high_water_maxrss": after.ru_maxrss,
        "rss_attribution": "RUSAGE_CHILDREN cumulative high-water mark",
    }


def expect_failure(label: str, fn: Callable[[], Any], contains: str) -> dict[str, str]:
    try:
        fn()
    except (RuntimeError, ValueError, json.JSONDecodeError) as error:
        detail = str(error)
        if contains not in detail:
            raise RuntimeError(f"{label}: wrong failure {detail!r}, wanted {contains!r}")
        return {"verdict": "REJECTED", "detail": detail}
    raise RuntimeError(f"{label}: control was accepted")


def replace_json(raw: str, key: str, value: Any) -> str:
    decoded = json.loads(raw)
    decoded[key] = value
    return json.dumps(decoded, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def decoder_controls(record: dict[str, Any]) -> dict[str, Any]:
    expected = ((record["module"], record["name"], record["kind"]),)
    exporter = record["exporter"]
    raw = record["record_utf8"]
    frame = native.FRAME + raw
    controls = {
        "missing": expect_failure("missing", lambda: native.parse_frames("", expected, exporter),
                                  "frame population"),
        "duplicate": expect_failure("duplicate", lambda: native.parse_frames(
            frame + "\n" + frame, expected, exporter), "frame population"),
        "truncated": expect_failure("truncated", lambda: native.parse_frames(
            native.FRAME + raw[:-1], expected, exporter), "Expecting"),
        "malformed_tag": expect_failure("malformed tag", lambda: native.parse_frames(
            native.FRAME + replace_json(raw, "type", ["futureExpr"]), expected, exporter),
            "unknown or malformed Expr tag"),
        "schema": expect_failure("schema", lambda: native.parse_frames(
            native.FRAME + replace_json(raw, "schema", "future/v9"), expected, exporter),
            "schema mismatch"),
        "toolchain": expect_failure("toolchain", lambda: native.parse_frames(
            native.FRAME + replace_json(raw, "toolchain", {
                "githash": "0" * 40, "version": "0.0.0"}), expected, exporter),
            "toolchain identity mismatch"),
        "exporter": expect_failure("exporter", lambda: native.parse_frames(
            native.FRAME + replace_json(raw, "exporter", "0" * 64), expected, exporter),
            "exporter mismatch"),
    }
    return controls


def lean_lookup_control(label: str, module: str, name: str, kind: str,
                        expected_text: str) -> dict[str, Any]:
    exporter_hash = native.sha256(native.EXPORTER)
    source = (
        "import Blanc.LidoCircuitBreakerPreControl\n" +
        native.EXPORTER.read_text(encoding="utf-8") +
        f'\n#blanc_native_identity "{module}" "{name}" "{kind}" "{exporter_hash}"\n'
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix=f"native-{label}-", dir=ROOT / "scripts",
        encoding="utf-8", delete=False,
    ) as handle:
        path = Path(handle.name)
        handle.write(source)
    try:
        with gate_semaphore.admitted(f"native-identity {label} negative control"):
            run = subprocess.run(["lake", "env", "lean", str(path.relative_to(ROOT))],
                                 cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
    finally:
        path.unlink(missing_ok=True)
    if run.returncode == 0 or expected_text not in run.stdout:
        raise RuntimeError(f"{label}: wrong Lean outcome ({run.returncode}):\n{run.stdout}")
    return {"exit": run.returncode, "verdict": "REJECTED", "matched": expected_text,
            "raw": run.stdout}


def classify_fixtures(records: dict[str, dict[str, Any]]) -> dict[str, Any]:
    get = lambda short: records[f"Blanc.LeanNativeIdentityPilot.Fixture.{short}"]
    comparisons = [
        ("proof_term_vs_tactic", "binderUniverseTerm", "binderUniverseTactic", True,
         "proof value and adjacent comments excluded"),
        ("strengthened_premise", "premiseBaseline", "strengthenedPremise", False,
         "additional explicit forall retained"),
        ("weakened_conclusion", "conclusionBaseline", "weakenedConclusion", False,
         "conclusion Expr retained"),
        ("gas_literal", "gasBaseline", "changedGas", False,
         "Nat literal retained"),
        ("implicit_binder", "explicitBinder", "implicitBinder", False,
         "BinderInfo retained"),
        ("strict_implicit_binder", "implicitBinder", "strictImplicitBinder", False,
         "BinderInfo retained"),
        ("instance_binder", "explicitBinder", "instanceBinder", False,
         "instance forall and BinderInfo retained"),
        ("universe_rename", "binderUniverseTerm", "universeRenamed", False,
         "universe parameter names retained"),
        ("universe_reorder", "binderUniverseTerm", "universeReordered", False,
         "declared universe order retained in statement record"),
        ("parenthesized_metadata_spelling", "explicitBinder", "metadataSpelling", True,
         "source/elaborator metadata removed"),
        ("referenced_alias", "directAlias", "referencedAlias", False,
         "referenced constant Name retained without unfolding"),
    ]
    out: dict[str, Any] = {}
    for label, left, right, should_equal, policy in comparisons:
        left_hash = get(left)["statement_sha256"]
        right_hash = get(right)["statement_sha256"]
        equal = left_hash == right_hash
        if equal != should_equal:
            raise RuntimeError(f"{label}: observed equal={equal}, expected {should_equal}")
        out[label] = {"left": left, "right": right, "equal": equal,
                      "expected_equal": should_equal, "policy": policy,
                      "left_sha256": left_hash, "right_sha256": right_hash}
    out["let_structure"] = {
        "name": "letType", "classification": "retained as Expr.letE; no reduction",
        "statement_sha256": get("letType")["statement_sha256"],
    }
    out["notation"] = {
        "name": "notationType", "classification": "compared after elaboration; source spelling absent",
        "statement_sha256": get("notationType")["statement_sha256"],
    }
    return out


def source_ledger(records: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for qualified, (relative, short, pinned) in ACTUAL.items():
        source = (ROOT / relative).read_text(encoding="utf-8")
        header = header_before_definition(source, short)
        header_hash = sha(header.encode())
        if header_hash != pinned:
            raise RuntimeError(f"{qualified}: source header pin drift {header_hash} != {pinned}")
        record = records[qualified]
        rows.append({
            "name": qualified, "owner_source": relative,
            "old_normalized_header": header, "old_header_sha256": header_hash,
            "native_record_utf8": record["record_utf8"],
            "native_record_sha256": record["record_sha256"],
            "native_statement_utf8": record["statement_utf8"],
            "native_statement_sha256": record["statement_sha256"],
            "native_type_utf8": record["type_utf8"],
            "native_type_sha256": record["type_sha256"],
            "owner_module": record["module"], "kind": record["kind"],
            "levelParams": record["levelParams"], "axioms": record["axioms"],
            "toolchain": record["toolchain"], "exporter": record["exporter"],
            "build_identity": record["build_identity"],
            "build_traces_sha256": record["build_traces_sha256"],
        })
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--skip-lean-lookup-controls", action="store_true")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    parser_controls()  # Reuse the production lexical fake/comment/string controls.
    cert_before = native.require_fresh_build_certificate()
    source_before = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                   check=True, text=True, capture_output=True).stdout.strip()
    measurements = [run_shadow("access", args.output_dir),
                    run_shadow("enumeration", args.output_dir)]
    all_records: dict[str, dict[str, Any]] = {}
    for scope in ("access", "enumeration"):
        for record in json.loads((args.output_dir / f"{scope}.json").read_text()):
            if record["name"] in all_records:
                raise RuntimeError(f"duplicate combined record {record['name']}")
            all_records[record["name"]] = record
    if set(ACTUAL) - set(all_records):
        raise RuntimeError(f"missing actual declarations {sorted(set(ACTUAL)-set(all_records))}")
    fixture = classify_fixtures(all_records)
    decoder = decoder_controls(all_records[next(iter(ACTUAL))])
    lean_controls: dict[str, Any] = {}
    if not args.skip_lean_lookup_controls:
        good = "Blanc.LidoCircuitBreaker.assignmentPost_assignment"
        lean_controls = {
            "wrong_qualified_name": lean_lookup_control(
                "wrong-name", "Blanc.LidoCircuitBreakerPreControl", good + "_missing",
                "theorem", "Unknown constant"),
            "wrong_module": lean_lookup_control(
                "wrong-module", "Blanc.LidoCircuitBreakerAccess", good,
                "theorem", "declaration module mismatch"),
            "wrong_kind": lean_lookup_control(
                "wrong-kind", "Blanc.LidoCircuitBreakerPreControl", good,
                "axiom", "declaration kind mismatch"),
        }
    cert_after = native.require_fresh_build_certificate()
    source_after = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                  check=True, text=True, capture_output=True).stdout.strip()
    if source_after != source_before or cert_after["identity"] != cert_before["identity"]:
        raise RuntimeError("source/build identity drifted during harness")
    ledger = {
        "schema": "blanc-lean-native-identity-shadow-evidence/v1",
        "mode": "SHADOW; all 259 production pins remain authoritative",
        "source_commit_before": source_before, "source_commit_after": source_after,
        "build_identity_before": cert_before["identity"],
        "build_identity_after": cert_after["identity"],
        "build_provenance": cert_after["provenance"],
        "exporter_sha256": native.sha256(native.EXPORTER),
        "declarations": source_ledger(all_records),
        "fixture_classifications": fixture,
        "decoder_controls": decoder,
        "lean_lookup_controls": lean_controls,
        "measurements": measurements,
        "unsupported": [
            "no mathematical equivalence or reduction",
            "no transitive semantic-body identity",
            "no all-259 migration or parser retirement",
            "no latency or memory saving claim",
        ],
    }
    destination = args.output_dir / "ledger.json"
    destination.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    print("OK — Lean-native identity shadow: 4 declarations; strict decoder, schema, "
          "fixture-classification and Lean lookup controls")


if __name__ == "__main__":
    main()
