#!/usr/bin/env python3
"""Live coherent mutations for all seven frozen differential families."""

from __future__ import annotations

import argparse
import copy
import sys
from pathlib import Path
from typing import Any, Callable, Dict, Mapping

from lido_ossifiable_proxy_differential_schema import (
    CASE_COUNT,
    EELS_COMMIT,
    EVALUATOR_RELATIVE,
    EXPECTED_CASE_IDS,
    EXPECTED_REFERENCE_ARTIFACTS,
    FALSIFIER_FAMILIES,
    LAUNCHER_RELATIVE,
    MANIFEST_DIGEST,
    MANIFEST_RELATIVE,
    PERFORMANCE_DIGEST,
    PERFORMANCE_RELATIVE,
    REFERENCE_LOCK_SHA256,
    RESULT_FORMAT,
    RUNNER_RELATIVE,
    SCHEMA_RELATIVE,
    ValidationError,
    load_and_validate_campaign,
    manifest_order_sha256,
    materialize_expected_projections,
    seal_campaign_for_test,
    seal_result,
    sha256_bytes,
    sha256_file,
    validate_manifest,
    validate_result,
)


def case(document: Mapping[str, Any], case_id: str) -> Dict[str, Any]:
    return next(row for row in document["cases"] if row["id"] == case_id)


def must_reject(label: str, operation: Callable[[], None], diagnostic: str) -> None:
    try:
        operation()
    except ValidationError as exc:
        if diagnostic not in str(exc):
            raise RuntimeError(
                f"{label} hit unexpected boundary: {exc}; wanted {diagnostic!r}"
            ) from exc
        return
    raise RuntimeError(f"falsifier survived: {label}")


def resealed_manifest_rejection(
    label: str,
    manifest: Mapping[str, Any],
    performance: Mapping[str, Any],
    reference: Mapping[str, Any],
    reference_path: Path,
    mutate: Callable[[Dict[str, Any]], None],
    diagnostic: str,
) -> None:
    candidate = copy.deepcopy(manifest)
    mutate(candidate)
    seal_campaign_for_test(candidate)
    must_reject(
        label,
        lambda: validate_manifest(
            candidate,
            performance,
            reference,
            reference_path,
            enforce_pinned_digest=False,
        ),
        diagnostic,
    )


def synthetic_result(
    repo_root: Path, manifest: Mapping[str, Any], performance: Mapping[str, Any]
) -> Dict[str, Any]:
    expected = materialize_expected_projections(manifest, performance)
    rows = [
        {
            "id": case_id,
            "ordinal": ordinal,
            "expected": copy.deepcopy(expected[case_id]),
            "reference": copy.deepcopy(expected[case_id]),
            "blanc": copy.deepcopy(expected[case_id]),
            "matches": True,
            "mismatches": [],
        }
        for ordinal, case_id in enumerate(EXPECTED_CASE_IDS, 1)
    ]
    result: Dict[str, Any] = {
        "schema": RESULT_FORMAT,
        "identity": {
            "manifestDigest": MANIFEST_DIGEST,
            "manifestPath": MANIFEST_RELATIVE.as_posix(),
            "manifestCaseCount": CASE_COUNT,
            "manifestOrderSha256": manifest_order_sha256(manifest),
            "performanceManifestDigest": PERFORMANCE_DIGEST,
            "performanceManifestSha256": sha256_file(repo_root / PERFORMANCE_RELATIVE),
            "referenceLockSha256": REFERENCE_LOCK_SHA256,
            "referenceArtifacts": {
                name: {"byteLength": length, "sha256": digest}
                for name, (length, digest) in EXPECTED_REFERENCE_ARTIFACTS.items()
            },
            "eels": {
                "callEntrypoint": "ethereum.prague.vm.interpreter.process_message_call",
                "commit": EELS_COMMIT,
                "createEntrypoint": "ethereum.prague.vm.interpreter.process_create_message",
                "fork": "Prague",
                "network": False,
                "python": "venv/bin/python",
                "pythonPath": "src",
                "rootEnv": "EELS_ROOT",
                "requiredEnvironment": {
                    "PYTHONDONTWRITEBYTECODE": "1",
                    "PYTHONPATH": "${EELS_ROOT}/src",
                },
            },
            "blanc": {
                "artifactEnvelopeSha256": "1" * 64,
                "commit": "2" * 40,
                "creationTemplate": {"byteLength": 1, "sha256": "3" * 64},
                "evaluatorPath": EVALUATOR_RELATIVE.as_posix(),
                "evaluatorSha256": "4" * 64,
                "repositoryClean": True,
                "returnedRuntime": {"byteLength": 1, "sha256": "5" * 64},
            },
            "implementation": {
                "launcherPath": LAUNCHER_RELATIVE.as_posix(),
                "launcherSha256": "8" * 64,
                "runnerPath": RUNNER_RELATIVE.as_posix(),
                "runnerSha256": "6" * 64,
                "schemaPath": SCHEMA_RELATIVE.as_posix(),
                "schemaSha256": "7" * 64,
            },
            "resultDigest": {
                "algorithm": "sha256",
                "canonicalization": 'json.dumps(parsed, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")',
                "scope": "the entire parsed result with /identity/resultDigest/value replaced by the empty string",
                "value": "",
            },
        },
        "summary": {
            "allCasesExecuted": True,
            "allMatched": True,
            "caseCount": CASE_COUNT,
            "executedCaseCount": CASE_COUNT,
            "matchedCaseCount": CASE_COUNT,
            "mismatchCaseCount": 0,
            "skippedCaseCount": 0,
        },
        "rows": rows,
    }
    seal_result(result)
    validate_result(result, manifest, performance=performance)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    args = parser.parse_args()
    root = args.repo_root.expanduser().resolve()
    manifest, performance, reference = load_and_validate_campaign(root)
    reference_path = root / "scripts/lido-ossifiable-proxy-reference.json"

    resealed_manifest_rejection(
        "reference-substitution",
        manifest,
        performance,
        reference,
        reference_path,
        lambda value: value["identities"]["reference"].__setitem__(
            "referenceLockSha256", "0" * 64
        ),
        "reference substitution binding drifted",
    )
    resealed_manifest_rejection(
        "selector-routing",
        manifest,
        performance,
        reference,
        reference_path,
        lambda value: case(value, "G01")["world"].__setitem__(
            "calldata", "performance:get-implementation"
        ),
        "selector routing drifted",
    )

    def mutate_error(value: Dict[str, Any]) -> None:
        blob = value["fixtures"]["errors"]["NotAdmin"]
        raw = bytearray.fromhex(blob["hex"][2:])
        raw[-1] ^= 1
        blob["hex"] = "0x" + raw.hex()
        blob["byteLength"] = len(raw)
        blob["sha256"] = sha256_bytes(bytes(raw))

    resealed_manifest_rejection(
        "event-error-bytes",
        manifest,
        performance,
        reference,
        reference_path,
        mutate_error,
        "event/error byte family drifted",
    )
    resealed_manifest_rejection(
        "state-projection",
        manifest,
        performance,
        reference,
        reference_path,
        lambda value: case(value, "K05")["expected"]["storage"].__setitem__(
            "implementation", "performance:canonical-implementation"
        ),
        "K05 both-slot constructor projection drifted",
    )
    resealed_manifest_rejection(
        "rollback",
        manifest,
        performance,
        reference,
        reference_path,
        lambda value: case(value, "X09")["expected"].__setitem__(
            "storage", {"base": "performance:unossified", "implementation": "performance:new-implementation"}
        ),
        "X09 rollback projection drifted",
    )
    resealed_manifest_rejection(
        "child-call-observation",
        manifest,
        performance,
        reference,
        reference_path,
        lambda value: case(value, "F07")["expected"]["delegatecalls"][0].__setitem__(
            "input", "differential:unknown-selector-4"
        ),
        "exact ordered DELEGATECALL projection bytes drifted",
    )
    resealed_manifest_rejection(
        "corpus-result-mutation/corpus",
        manifest,
        performance,
        reference,
        reference_path,
        lambda value: value["cases"].__delitem__(-1),
        "manifest case count drifted",
    )
    result = synthetic_result(root, manifest, performance)
    mutated_result = copy.deepcopy(result)
    for field in ("expected", "reference", "blanc"):
        mutated_result["rows"][0][field]["status"] = "revert"
    seal_result(mutated_result)
    must_reject(
        "corpus-result-mutation/result",
        lambda: validate_result(
            mutated_result, manifest, performance=performance
        ),
        "K01 result expected projection drifted from the manifest",
    )
    skipped_result = copy.deepcopy(result)
    skipped_result["rows"].pop()
    skipped_result["summary"].update({
        "allCasesExecuted": False,
        "caseCount": CASE_COUNT - 1,
        "executedCaseCount": CASE_COUNT - 1,
        "matchedCaseCount": CASE_COUNT - 1,
        "skippedCaseCount": 1,
    })
    seal_result(skipped_result)
    must_reject(
        "corpus-result-mutation/skipped-row",
        lambda: validate_result(skipped_result, manifest, performance=performance),
        "result row count drifted",
    )

    if FALSIFIER_FAMILIES != {
        "reference-substitution",
        "selector-routing",
        "event-error-bytes",
        "state-projection",
        "rollback",
        "child-call-observation",
        "corpus-result-mutation",
    }:
        raise RuntimeError("test ownership drifted from the seven manifest families")
    print(
        "OK — OssifiableProxy differential falsifiers: 7/7 families rejected; "
        "9 coherent manifest/result mutations; no EELS execution"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(
            "REGRESSION — OssifiableProxy differential falsifiers: "
            + str(exc).replace("\n", " "),
            file=sys.stderr,
        )
        raise SystemExit(1)
