#!/usr/bin/env python3
"""Live deletion/coherent-edit controls for the artifact profile baseline."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
from pathlib import Path

from lido_circuit_breaker_artifact_profile_schema import validate_profile


REPO = Path(__file__).resolve().parents[1]
LEDGER = REPO / "scripts" / "fixtures" / "lido-circuit-breaker" / "artifact-profile-baseline.json"
EXPECTED_LEDGER_SHA256 = "b0a59c180afac1cb1b853b747696523334c774f269001492b9109012ce6f9e7f"


def rejected(value) -> bool:
    try:
        validate_profile(value)
    except (KeyError, RuntimeError, TypeError, ValueError):
        return True
    return False


def main() -> int:
    if not LEDGER.is_file():
        raise RuntimeError("committed artifact profile baseline is missing")
    raw = LEDGER.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED_LEDGER_SHA256:
        raise RuntimeError("independently pinned artifact profile identity drifted")
    baseline = json.loads(raw)
    validate_profile(baseline)

    mutations = []
    broken = copy.deepcopy(baseline); del broken["gasClasses"]
    mutations.append(("top-level deletion", broken))
    broken = copy.deepcopy(baseline); del broken["artifacts"]["blanc"]["runtime"]["regions"][1]
    mutations.append(("layout-region deletion", broken))
    broken = copy.deepcopy(baseline); broken["artifacts"]["blanc"]["runtime"]["regions"][1]["start"] += 1
    mutations.append(("layout gap", broken))
    broken = copy.deepcopy(baseline)
    broken["artifacts"]["blanc"]["identities"]["officialRuntime"]["sha256"] = "00" * 32
    broken["artifacts"]["blanc"]["runtime"]["sha256"] = "00" * 32
    mutations.append(("coherent artifact-digest edit", broken))
    broken = copy.deepcopy(baseline); broken["provenance"]["baselineManifest"]["sha256"] = "11" * 32
    mutations.append(("baseline-manifest laundering", broken))
    broken = copy.deepcopy(baseline); broken["artifacts"]["blanc"]["layoutEvidence"]["runtimeTable"][0]["byteLength"] -= 1
    mutations.append(("evaluator-layout coherent edit", broken))
    broken = copy.deepcopy(baseline); broken["artifacts"]["blanc"]["layoutEvidence"]["runtimeEndpoints"][0]["start"] += 1
    mutations.append(("endpoint-layout coherent edit", broken))
    broken = copy.deepcopy(baseline); broken["gasClasses"]["GAS-3"]["rows"][0]["endpoint"] = "relabelled()"
    mutations.append(("gas-vector relabel", broken))
    broken = copy.deepcopy(baseline); broken["artifacts"]["blanc"]["runtime"]["regions"][0]["owner"] = "unknown"
    mutations.append(("ownership erasure", broken))
    broken = copy.deepcopy(baseline); del broken["artifacts"]["solidity"]["runtime"]["disassembly"]["instructionStreamSha256"]
    mutations.append(("disassembly deletion", broken))

    missed = [name for name, mutation in mutations if not rejected(mutation)]
    if missed:
        raise RuntimeError("artifact profile falsifier(s) passed: " + ", ".join(missed))
    print(f"OK — Lido artifact profile falsifiers: {len(mutations)} deletion/layout/digest/manifest/gas/owner/disassembly controls rejected")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print("REGRESSION — Lido artifact profile falsifiers: " + str(exc).replace("\n", " "),
              file=sys.stderr)
        raise SystemExit(1)
