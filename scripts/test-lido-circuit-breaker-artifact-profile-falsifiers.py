#!/usr/bin/env python3
"""Live deletion/coherent-edit controls for both Lido artifact ledgers."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
from pathlib import Path

from lido_circuit_breaker_artifact_profile_schema import (
    validate_optimized_profile, validate_profile,
)


REPO = Path(__file__).resolve().parents[1]
FIXTURES = REPO / "scripts" / "fixtures" / "lido-circuit-breaker"
BASELINE_LEDGER = FIXTURES / "artifact-profile-baseline.json"
OPTIMIZED_LEDGER = FIXTURES / "artifact-profile-optimized.json"
EXPECTED_BASELINE_LEDGER_SHA256 = "b0a59c180afac1cb1b853b747696523334c774f269001492b9109012ce6f9e7f"
EXPECTED_OPTIMIZED_LEDGER_SHA256 = "ba3a0d93118ff80453920d6f05801ab25d9c232f3bba7471e39936931b1a8920"


def rejected(value, validator) -> bool:
    try:
        validator(value)
    except (KeyError, RuntimeError, TypeError, ValueError):
        return True
    return False


def main() -> int:
    if not BASELINE_LEDGER.is_file():
        raise RuntimeError("committed artifact profile baseline is missing")
    baseline_raw = BASELINE_LEDGER.read_bytes()
    if hashlib.sha256(baseline_raw).hexdigest() != EXPECTED_BASELINE_LEDGER_SHA256:
        raise RuntimeError("independently pinned artifact profile identity drifted")
    baseline = json.loads(baseline_raw)
    validate_profile(baseline)
    if not OPTIMIZED_LEDGER.is_file():
        raise RuntimeError("committed optimized artifact profile is missing")
    optimized_raw = OPTIMIZED_LEDGER.read_bytes()
    if hashlib.sha256(optimized_raw).hexdigest() != EXPECTED_OPTIMIZED_LEDGER_SHA256:
        raise RuntimeError("independently pinned optimized artifact profile identity drifted")
    optimized = json.loads(optimized_raw)
    validate_optimized_profile(optimized)

    baseline_mutations = []
    broken = copy.deepcopy(baseline); del broken["gasClasses"]
    baseline_mutations.append(("baseline top-level deletion", broken))
    broken = copy.deepcopy(baseline); del broken["artifacts"]["blanc"]["runtime"]["regions"][1]
    baseline_mutations.append(("baseline layout-region deletion", broken))
    broken = copy.deepcopy(baseline); broken["artifacts"]["blanc"]["runtime"]["regions"][1]["start"] += 1
    baseline_mutations.append(("baseline layout gap", broken))
    broken = copy.deepcopy(baseline)
    broken["artifacts"]["blanc"]["identities"]["officialRuntime"]["sha256"] = "00" * 32
    broken["artifacts"]["blanc"]["runtime"]["sha256"] = "00" * 32
    baseline_mutations.append(("baseline coherent artifact-digest edit", broken))
    broken = copy.deepcopy(baseline); broken["provenance"]["baselineManifest"]["sha256"] = "11" * 32
    baseline_mutations.append(("baseline-manifest laundering", broken))
    broken = copy.deepcopy(baseline); broken["artifacts"]["blanc"]["layoutEvidence"]["runtimeTable"][0]["byteLength"] -= 1
    baseline_mutations.append(("baseline evaluator-layout coherent edit", broken))
    broken = copy.deepcopy(baseline); broken["artifacts"]["blanc"]["layoutEvidence"]["runtimeEndpoints"][0]["start"] += 1
    baseline_mutations.append(("baseline endpoint-layout coherent edit", broken))
    broken = copy.deepcopy(baseline); broken["gasClasses"]["GAS-3"]["rows"][0]["endpoint"] = "relabelled()"
    baseline_mutations.append(("baseline gas-vector relabel", broken))
    broken = copy.deepcopy(baseline); broken["artifacts"]["blanc"]["runtime"]["regions"][0]["owner"] = "unknown"
    baseline_mutations.append(("baseline ownership erasure", broken))
    broken = copy.deepcopy(baseline); del broken["artifacts"]["solidity"]["runtime"]["disassembly"]["instructionStreamSha256"]
    baseline_mutations.append(("baseline disassembly deletion", broken))

    optimized_mutations = []
    broken = copy.deepcopy(optimized); del broken["beforeAfter"]
    optimized_mutations.append(("optimized attribution deletion", broken))
    broken = copy.deepcopy(optimized)
    broken["provenance"]["baselineLedger"]["sha256"] = "22" * 32
    optimized_mutations.append(("frozen-ledger laundering", broken))
    broken = copy.deepcopy(optimized)
    broken["artifacts"]["blanc"]["identities"]["officialRuntime"]["sha256"] = "33" * 32
    broken["artifacts"]["blanc"]["runtime"]["sha256"] = "33" * 32
    optimized_mutations.append(("optimized coherent artifact-digest edit", broken))
    broken = copy.deepcopy(optimized)
    del broken["artifacts"]["blanc"]["runtime"]["regions"][1]
    optimized_mutations.append(("optimized layout-region deletion", broken))
    broken = copy.deepcopy(optimized)
    broken["artifacts"]["blanc"]["runtime"]["regions"][1]["start"] += 1
    optimized_mutations.append(("optimized layout gap", broken))
    broken = copy.deepcopy(optimized)
    broken["artifacts"]["blanc"]["layoutEvidence"]["runtimeTable"][0]["byteLength"] -= 1
    optimized_mutations.append(("optimized runtime-table coherent edit", broken))
    broken = copy.deepcopy(optimized)
    broken["artifacts"]["blanc"]["layoutEvidence"]["runtimeEndpoints"][0]["start"] += 1
    optimized_mutations.append(("optimized endpoint-layout coherent edit", broken))
    broken = copy.deepcopy(optimized)
    broken["artifacts"]["blanc"]["layoutEvidence"]["immutableOffsets"]["admin"][0] += 1
    optimized_mutations.append(("optimized immutable-lane edit", broken))
    broken = copy.deepcopy(optimized)
    del broken["artifacts"]["blanc"]["layoutEvidence"]["fixedCoordinatePushes"][0]
    optimized_mutations.append(("optimized coordinate-push deletion", broken))
    broken = copy.deepcopy(optimized)
    broken["beforeAfter"]["artifactSizes"]["runtime"]["deltaBytes"] += 1
    optimized_mutations.append(("optimized before-after coherent edit", broken))
    broken = copy.deepcopy(optimized)
    broken["artifacts"]["blanc"]["runtime"]["regions"][0]["owner"] = "Lido-private"
    optimized_mutations.append(("optimized ownership relabel", broken))
    broken = copy.deepcopy(optimized)
    broken["ownershipSummary"]["Blanc-common"]["blancArtifactBytes"] += 1
    broken["ownershipSummary"]["Lido-private"]["blancArtifactBytes"] -= 1
    optimized_mutations.append(("optimized ownership-summary transfer", broken))
    broken = copy.deepcopy(optimized)
    broken["ownershipSummary"]["Blanc-common"]["basis"] = "hand-maintained total"
    optimized_mutations.append(("optimized ownership-summary basis edit", broken))
    broken = copy.deepcopy(optimized)
    del broken["artifacts"]["solidity"]["runtime"]["disassembly"]["instructionStreamSha256"]
    optimized_mutations.append(("optimized disassembly deletion", broken))

    missed = [name for name, mutation in baseline_mutations
              if not rejected(mutation, validate_profile)]
    missed += [name for name, mutation in optimized_mutations
               if not rejected(mutation, validate_optimized_profile)]
    if missed:
        raise RuntimeError("artifact profile falsifier(s) passed: " + ", ".join(missed))
    total = len(baseline_mutations) + len(optimized_mutations)
    print(f"OK — Lido artifact profile falsifiers: {total} frozen/optimized deletion/layout/digest/laundering/attribution/owner/disassembly controls rejected")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print("REGRESSION — Lido artifact profile falsifiers: " + str(exc).replace("\n", " "),
              file=sys.stderr)
        raise SystemExit(1)
