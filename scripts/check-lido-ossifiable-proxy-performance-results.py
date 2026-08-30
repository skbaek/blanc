#!/usr/bin/env python3
"""Statically validate immutable OssifiableProxy performance result bundles."""
from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path
from types import ModuleType

import lido_ossifiable_proxy_performance_schema as schema


def load_runner() -> ModuleType:
    path = Path(__file__).with_name("run-lido-ossifiable-proxy-performance.py")
    spec = importlib.util.spec_from_file_location("ossifiable_performance_runner", path)
    if spec is None or spec.loader is None:
        raise schema.SchemaError(f"cannot load performance evidence validator {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def load_result(path: Path, manifest: dict, root: Path) -> dict:
    _, value = schema.load_json(path, f"performance result {path}")
    return schema.validate_result_schema(
        value,
        manifest,
        root=root,
        enforce_self_digest=True,
        validate_external=True,
    )


def validate_evidence_bundle(
    runner: ModuleType,
    directory: Path,
    result: dict,
    manifest: dict,
    root: Path,
) -> None:
    expected_names = {f"{cell_id}.json" for cell_id in schema.CELL_ORDER} | {
        "diagnostics.json"
    }
    if not directory.is_dir():
        raise schema.SchemaError(f"performance evidence directory is missing: {directory}")
    actual_names = {path.name for path in directory.iterdir()}
    if actual_names != expected_names:
        raise schema.SchemaError(
            "performance evidence membership differs: "
            f"expected {sorted(expected_names)}, found {sorted(actual_names)}"
        )
    expected_implementation = runner._implementation_identity(root)
    evidence_hashes: dict[str, str] = {}
    evidence_records: dict[str, dict] = {}
    envelope_digest: str | None = None
    for index, cell_id in enumerate(schema.CELL_ORDER):
        path = directory / f"{cell_id}.json"
        raw, value = schema.load_json(path, f"performance evidence {cell_id}")
        digest = runner.sha256_bytes(raw)
        if digest != result["cells"][index]["evidence"]["recordSha256"]:
            raise schema.SchemaError(f"performance evidence {cell_id}: ledger digest differs")
        runner.validate_evidence_record(
            value, manifest=manifest, result=result, cell_index=index
        )
        implementation = value["identities"].get("implementation")
        if implementation != expected_implementation:
            raise schema.SchemaError(
                f"performance evidence {cell_id}: evaluator/runner/schema identity differs"
            )
        candidate = value["identities"].get("evaluatorEnvelopeSha256")
        if not isinstance(candidate, str) or len(candidate) != 64:
            raise schema.SchemaError(
                f"performance evidence {cell_id}: evaluator envelope digest malformed"
            )
        if envelope_digest is None:
            envelope_digest = candidate
        elif envelope_digest != candidate:
            raise schema.SchemaError(
                f"performance evidence {cell_id}: evaluator envelope identity differs"
            )
        evidence_hashes[cell_id] = digest
        evidence_records[cell_id] = value

    diagnostics_path = directory / "diagnostics.json"
    diagnostics_raw, diagnostics = schema.load_json(
        diagnostics_path, "performance diagnostics"
    )
    diagnostic_digest = runner.sha256_bytes(diagnostics_raw)
    diagnostic_rows = result["diagnostics"]
    if diagnostic_rows != [{
        "name": "primary-prague-measurement-diagnostics",
        "recordSha256": diagnostic_digest,
    }]:
        raise schema.SchemaError("performance diagnostics ledger digest differs")
    runner.validate_diagnostics_record(
        diagnostics,
        manifest=manifest,
        result=result,
        evidence_hashes=evidence_hashes,
        evidence_records=evidence_records,
        lock=schema.strict_json(
            (root / schema.REFERENCE_LOCK_RELATIVE).read_bytes(),
            "performance diagnostics reference lock",
        ),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=schema.DEFAULT_ROOT)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument(
        "--result", type=Path, action="append", required=True,
        help="immutable baseline or final ledger; may be repeated",
    )
    parser.add_argument(
        "--evidence", type=Path, action="append", required=True,
        help="evidence directory paired positionally with --result; may be repeated",
    )
    parser.add_argument("--require-final-threshold", action="store_true")
    args = parser.parse_args()
    root = args.root.expanduser().resolve()
    manifest_path = (
        args.manifest.expanduser().resolve()
        if args.manifest else root / schema.MANIFEST_RELATIVE
    )
    try:
        if len(args.result) != len(args.evidence):
            raise schema.SchemaError("each --result requires one positionally paired --evidence")
        _, manifest_value = schema.load_json(manifest_path, "performance manifest")
        manifest = schema.validate_manifest_schema(
            manifest_value,
            root=root,
            enforce_frozen_digest=True,
            validate_external=True,
        )
        runner = load_runner()
        results: list[dict] = []
        for result_path, evidence_path in zip(args.result, args.evidence):
            result = load_result(result_path.expanduser().resolve(), manifest, root)
            validate_evidence_bundle(
                runner,
                evidence_path.expanduser().resolve(),
                result,
                manifest,
                root,
            )
            results.append(result)
        stages = [result["result"]["stage"] for result in results]
        if len(stages) != len(set(stages)):
            raise schema.SchemaError("at most one baseline and one final result are allowed")
        if "baseline" in stages and "final" in stages:
            baseline = results[stages.index("baseline")]
            final = results[stages.index("final")]
            if final["result"]["predecessorResultSha256"] != \
                    baseline["result"]["digest"]["value"]:
                raise schema.SchemaError(
                    "final result predecessor does not equal the baseline canonical self-digest"
                )
        if args.require_final_threshold:
            if "final" not in stages:
                raise schema.SchemaError(
                    "--require-final-threshold needs a supplied final result"
                )
            schema.require_final_threshold(results[stages.index("final")])
    except (OSError, schema.SchemaError, RuntimeError) as exc:
        print(
            f"REGRESSION — OssifiableProxy performance evidence: {exc}",
            file=sys.stderr,
        )
        return 1
    print(
        "OK — OssifiableProxy performance evidence: "
        f"{len(results)} immutable result bundle(s); 25 ordered cell records each; "
        "identities, scalar formulae, semantic projections, evidence hashes, and lineage valid; "
        "no measurements run"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
