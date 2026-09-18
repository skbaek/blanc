#!/usr/bin/env python3
"""Independent schema, semantic, and falsifier checks for DRIP oracle vectors."""

from __future__ import annotations

import argparse
import copy
import json
import random
import sys
from pathlib import Path
from typing import Any, Callable

from drip_oracle import (
    ADDRESS_MAX,
    CHI_SLOT,
    HALF,
    MAX_ASSET,
    MAX_CHI,
    MAX_ELAPSED,
    MAX_PIE,
    MAX_UNITS,
    PIE_SLOT,
    RATE,
    RHO_SLOT,
    SCALE,
    WORD_MODULUS,
    Drip,
    Revert,
    assets_for_units,
    exit_residue,
    fresh_index,
    join_residue,
    operation_count,
    rpow_checked,
    segment_index,
    units_for_assets,
)


ROOT = Path(__file__).resolve().parents[1]
VECTORS = ROOT / "scripts" / "drip-oracle-vectors.json"
YEAR = 31_536_000
ALICE = 0xA11CE
BOB = 0xB0B
CAROL = 0xCA201

OBLIGATIONS = [
    "deployment-genesis", "drip-same-timestamp", "drip-local-under-k2",
    "drip-local-over-k3", "drip-one-year", "drip-max-elapsed",
    "drip-elapsed-overflow-revert", "drip-timestamp-regression-revert",
    "drip-chi-below-scale-revert", "drip-chi-above-cap-revert",
    "drip-post-chi-cap-boundary", "drip-post-chi-cap-revert",
    "join-zero-value", "join-genesis-first", "join-future-auto-drip",
    "join-max-asset", "join-over-max-asset-revert",
    "join-total-or-row-cap-revert", "join-zero-unit-credit",
    "exit-zero-unit-call", "exit-partial", "exit-full",
    "exit-future-auto-drip", "exit-insufficient-units-revert",
    "exit-underfunded-call-rollback", "exit-rejecting-recipient-rollback",
    "exit-successful-reentry", "view-units-fresh-consistency",
    "view-assets-fresh-consistency", "view-arithmetic-cap-boundaries",
    "receive-value-donation", "receive-zero-value", "unknown-selector-revert",
    "short-and-trailing-calldata-revert", "value-bearing-nonpayable-revert",
    "multi-participant-conservation", "segmentation-k3-versus-k1-k2",
    "receipt-returndata-log-matrix",
]


class CheckError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CheckError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_vectors() -> dict[str, Any]:
    try:
        value = json.loads(VECTORS.read_text(encoding="utf-8"),
                           object_pairs_hook=strict_object)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise CheckError(f"cannot parse {VECTORS.relative_to(ROOT)}: {error}") from error
    require(isinstance(value, dict), "vector root is not an object")
    return value


def require_keys(value: dict[str, Any], expected: set[str], label: str) -> None:
    require(set(value) == expected,
            f"{label} keys drifted: missing={sorted(expected-set(value))}, "
            f"extra={sorted(set(value)-expected)}")


def no_floats(value: Any, path: str = "$") -> None:
    if isinstance(value, float):
        raise CheckError(f"floating-point value at {path}")
    if isinstance(value, dict):
        for key, child in value.items():
            no_floats(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            no_floats(child, f"{path}[{index}]")


def validate_vectors(root: dict[str, Any]) -> None:
    require_keys(root, {
        "accountingVector", "boundaryCallVectors", "constants", "factorVectors",
        "guardVectors", "meta", "mutationControls", "roundingWitnesses",
        "scenarioObligations", "segmentVectors", "surfaceVectors", "transcripts",
        "viewVectors",
    }, "root")
    no_floats(root)

    require(root["meta"] == {
        "schema": 1,
        "generator": "scripts/gen-drip-oracle-vectors.py",
        "model": "scripts/drip_oracle.py",
        "arithmetic": "unbounded Python integers plus explicit 256-bit guards",
        "claimBoundary": "falsifier and fixture oracle; not Lean or EVM proof evidence",
    }, "metadata drifted")
    require(root["scenarioObligations"] == OBLIGATIONS,
            "38-obligation inventory or order drifted")
    require(root["constants"] == {
        "S": SCALE, "R": RATE, "H": HALF,
        "maxElapsed": MAX_ELAPSED, "maxChi": MAX_CHI,
        "maxAsset": MAX_ASSET, "maxUnits": MAX_UNITS, "maxPie": MAX_PIE,
        "chiSlot": CHI_SLOT, "rhoSlot": RHO_SLOT, "PieSlot": PIE_SLOT,
    }, "constant or storage identity drifted")

    factors = root["factorVectors"]
    require(isinstance(factors, list) and len(factors) == 6,
            "factor vector population is not six")
    expected_factors = {
        0: (SCALE, 0),
        1: (RATE, 0),
        2: (1_000_000_003_094_251_918_120_023_625, 2),
        3: (1_000_000_004_641_377_880_770_433_536, 2),
        YEAR: (1_049_999_999_999_999_999_961_070_145, 34),
        MAX_ELAPSED: (768_818_856_951_536_117_615_218_517_260, 62),
    }
    require([row.get("elapsed") for row in factors] == list(expected_factors),
            "factor-vector elapsed order drifted")
    for row in factors:
        require_keys(row, {"elapsed", "factor", "operationCount",
                           "operationKinds", "largestProduct"}, "factor row")
        expected_factor, expected_ops = expected_factors[row["elapsed"]]
        require((row["factor"], row["operationCount"]) ==
                (expected_factor, expected_ops),
                f"factor/operation drift at elapsed {row['elapsed']}")
        require(len(row["operationKinds"]) == expected_ops,
                f"operation-kind population drift at {row['elapsed']}")

    require(root["roundingWitnesses"] == {
        "under": {"elapsed": 2, "kind": "square",
                  "scaledError": -494_162_619_157_761_202_382_152_704},
        "over": {"elapsed": 3, "kind": "multiply",
                 "scaledError": 308_476_035_340_184_723_845_916_000},
    }, "local rounding witnesses drifted")

    guards = root["guardVectors"]
    require(guards["lastAcceptedChi"] ==
            442_604_085_272_050_989_502_489_636_102_618_752,
            "last accepted chi drifted")
    require(guards["lastAcceptedFreshChi"] ==
            340_282_366_920_938_463_463_374_607_431_768_211_167,
            "accepted cap-boundary result drifted")
    require(guards["firstRejectedChi"] == guards["lastAcceptedChi"] + 1,
            "first rejected chi is not adjacent")
    require(guards["firstRejectedReason"] == "fresh-chi-over-cap",
            "post-chi guard identity drifted")
    require(guards["maxAssetScaleBits"] == 218 and
            guards["maxUnitsChiBits"] == 256,
            "word-product bit evidence drifted")

    segment = root["segmentVectors"]
    require(segment == {
        "initialChi": SCALE,
        "singleParts": [3], "splitParts": [1, 2],
        "singleIndex": 1_000_000_004_641_377_880_770_433_536,
        "splitIndex": 1_000_000_004_641_377_880_770_433_535,
        "spread": 1, "certifiedBound": 4,
    }, "segmentation witness drifted")

    controls = root["mutationControls"]
    require(set(controls) == {
        "halfUpDiffersFromFloor", "segmentCompositionDiffersFromHalfUp",
        "autoDripChangesJoin", "joinFloorDiffersFromCeiling",
        "exitFloorDiffersFromCeiling", "k3FactorNontrivial",
    } and all(value is True for value in controls.values()),
            "arithmetic mutation controls do not all bite")

    boundary = {row.get("label"): row for row in root["boundaryCallVectors"]}
    expected_boundary = {
        "drip-elapsed-overflow-revert": ("revert", "elapsed-over-cap"),
        "drip-timestamp-regression-revert": ("revert", "timestamp-regression"),
        "drip-chi-below-scale-revert": ("revert", "stored-chi-out-of-range"),
        "drip-chi-above-cap-revert": ("revert", "stored-chi-out-of-range"),
        "drip-post-chi-cap-boundary": ("success", None),
        "drip-post-chi-cap-revert": ("revert", "fresh-chi-over-cap"),
        "join-max-asset": ("success", None),
        "join-over-max-asset-revert": ("revert", "asset-over-cap"),
        "join-total-or-row-cap-revert": ("revert", "caller-row-result-over-cap"),
        "join-zero-unit-credit": ("success", None),
        "exit-insufficient-units-revert": ("revert", "insufficient-caller-units"),
    }
    require(set(boundary) == set(expected_boundary), "boundary call inventory drifted")
    for label, (status, reason) in expected_boundary.items():
        require(boundary[label]["status"] == status, f"{label}: status drifted")
        if reason is not None:
            require(boundary[label].get("reason") == reason,
                    f"{label}: guard precedence drifted")
        if status == "revert":
            require(boundary[label]["pre"] == boundary[label]["post"],
                    f"{label}: rollback evidence drifted")
    require(boundary["join-zero-unit-credit"]["result"] == 0,
            "zero-unit join no longer returns zero")

    transcripts = root["transcripts"]
    failures = {row["label"]: row for row in transcripts["failureAndReentry"]}
    require(failures["exit-underfunded-call-rollback"]["status"] == "revert" and
            failures["exit-underfunded-call-rollback"]["reason"] ==
            "outbound-call-failed", "underfunded CALL row drifted")
    require(failures["exit-rejecting-recipient-rollback"]["status"] == "revert" and
            failures["exit-rejecting-recipient-rollback"]["pre"] ==
            failures["exit-rejecting-recipient-rollback"]["post"],
            "rejecting recipient rollback row drifted")
    require(failures["exit-successful-reentry"]["status"] == "success",
            "successful reentry row drifted")
    require(transcripts["zeroUnitRecipientCalls"] == 1,
            "zero-unit CALL observation drifted")

    views = root["viewVectors"]
    require(views["viewStatePreserved"] is True and
            views["unitPreview"] == views["sameStateJoinResult"] and
            views["sameStateExitPreview"] == views["sameStateExitResult"],
            "view/mutation consistency drifted")
    for row in root["surfaceVectors"]:
        require(0 <= row["joinResidue"] < row["chi"],
                "join residue outside divisor")
        require(0 <= row["exitResidue"] < SCALE,
                "exit residue outside scale")

    accounting = root["accountingVector"]
    terms = accounting["terms"]
    require_keys(terms, {
        "initialUnitsTimesChi", "accrual", "joinAssets", "joinResidue",
        "paidAssets", "exitResidue", "finalUnitsTimesChi", "lhs", "rhs",
        "outsideCredit",
    }, "accounting terms")
    recomputed_lhs = (terms["finalUnitsTimesChi"] + terms["joinResidue"] +
                      SCALE * terms["paidAssets"] + terms["exitResidue"])
    recomputed_rhs = (terms["initialUnitsTimesChi"] + terms["accrual"] +
                      SCALE * terms["joinAssets"])
    require(terms["lhs"] == recomputed_lhs == terms["rhs"] == recomputed_rhs,
            "coalition equality or one of its named terms drifted")
    require(terms["initialUnitsTimesChi"] > 0,
            "accounting vector lost its nonzero initial entitlement")


def expect_revert(reason: str, action: Callable[[], object]) -> None:
    try:
        action()
    except Revert as error:
        require(error.reason == reason,
                f"expected {reason!r}, received {error.reason!r}")
        return
    raise CheckError(f"expected revert {reason!r}, call succeeded")


def check_arithmetic_semantics() -> int:
    checks = 0
    for exponent in range(4097):
        factor, steps = rpow_checked(RATE, exponent)
        require(len(steps) == operation_count(exponent),
                f"operation count mismatch at {exponent}")
        for step in steps:
            require(step.product == step.left * step.right,
                    f"product mismatch at {exponent}")
            require(step.result == (step.product + HALF) // SCALE,
                    f"half-up mismatch at {exponent}")
            require(step.product + HALF < WORD_MODULUS,
                    f"unguarded word overflow at {exponent}")
            checks += 3
        fresh = fresh_index(SCALE, 0, exponent)
        require(SCALE * factor == SCALE * fresh.value + fresh.composition_residue,
                f"composition identity mismatch at {exponent}")
        require(0 <= fresh.composition_residue < SCALE,
                f"composition residue mismatch at {exponent}")
        checks += 3

    for exponent in (0, 1, 2, 3, YEAR, MAX_ELAPSED):
        zero, steps = rpow_checked(0, exponent)
        require(zero == (SCALE if exponent == 0 else 0) and not steps,
                f"zero-base edge mismatch at {exponent}")
        checks += 1

    random_source = random.Random(20260903 ^ 0xA817)
    for _ in range(10_000):
        chi = random_source.randrange(SCALE, MAX_CHI + 1)
        assets = random_source.randrange(MAX_ASSET + 1)
        units = random_source.randrange(MAX_UNITS + 1)
        minted = units_for_assets(assets, chi)
        payout = assets_for_units(units, chi)
        require(assets * SCALE == minted * chi + join_residue(assets, minted, chi),
                "random join identity failed")
        require(units * chi == payout * SCALE + exit_residue(units, payout, chi),
                "random exit identity failed")
        checks += 2
    return checks


def check_state_semantics() -> int:
    checks = 0
    model = Drip(100)
    baseline = model.snapshot()
    model.convert_to_units(7, 103)
    model.convert_to_assets(7, 103)
    require(model.snapshot() == baseline, "views mutated state")
    checks += 1

    expect_revert("elapsed-over-cap", lambda: model.drip(100 + MAX_ELAPSED + 1))
    require(model.snapshot() == baseline, "elapsed failure did not roll back")
    checks += 2
    expect_revert("asset-over-cap", lambda: model.join(ALICE, MAX_ASSET + 1, 100))
    require(model.snapshot() == baseline, "failed join retained incoming value")
    checks += 2

    model.join(ALICE, 10**24, 100)
    outer_pre = model.snapshot()
    saw_debit = False

    def reject_after_reentry(current: Drip, _payout: int) -> bool:
        nonlocal saw_debit
        saw_debit = current.row(ALICE) == 10**24 - 1
        current.join(BOB, 99, 103)
        return False

    expect_revert(
        "outbound-call-failed",
        lambda: model.exit(ALICE, 1, 103, reject_after_reentry),
    )
    require(saw_debit, "callback did not observe outer checks-effects state")
    require(model.snapshot() == outer_pre and model.row(BOB) == 0,
            "failed outer frame retained outer or nested effects")
    checks += 3

    calls = 0

    def accept_zero(_current: Drip, payout: int) -> bool:
        nonlocal calls
        calls += 1
        return payout == 0

    require(model.exit(ALICE, 0, 100, accept_zero) == 0 and calls == 1,
            "zero-unit exit skipped or changed the outbound CALL")
    require(model.Pie == sum(model.rows.values()), "ledger conservation failed")
    checks += 2
    return checks


def check_random_accounting() -> int:
    rng = random.Random(20260903 ^ 0xACC0)
    actors = (ALICE, BOB, CAROL)
    coalition = {ALICE, CAROL}
    checks = 0
    for trial in range(64):
        model = Drip(0)
        now = 0
        for actor in actors:
            model.join(actor, rng.randrange(1, 10**15), now)
        initial = model.snapshot()
        initial_units = sum(model.row(actor) for actor in coalition)
        initial_chi = model.chi
        acc = joined = paid = join_res = exit_res = 0
        total_join = total_paid = outside = 0

        def units_in(snapshot: dict[str, object]) -> int:
            rows = snapshot["rows"]
            return sum(int(rows.get(f"0x{actor:040x}", 0)) for actor in coalition)

        for _ in range(40):
            choice = rng.randrange(4)
            if choice == 3:
                credit = rng.randrange(1, 10**15)
                model.external_credit(credit)
                outside += credit
                continue
            now += rng.randrange(0, 8)
            pre = model.snapshot()
            if choice == 0:
                model.drip(now)
            elif choice == 1:
                actor = rng.choice(actors)
                assets = rng.randrange(0, 10**15)
                units = model.join(actor, assets, now)
                total_join += assets
                if actor in coalition:
                    joined += assets
                    join_res += join_residue(assets, units, model.chi)
            else:
                actor = rng.choice(actors)
                available = model.row(actor)
                units = rng.randrange(available + 1)
                payout = model.exit(actor, units, now)
                total_paid += payout
                if actor in coalition:
                    paid += payout
                    exit_res += exit_residue(units, payout, model.chi)
            acc += units_in(pre) * (model.chi - int(pre["chi"]))

        final_units = sum(model.row(actor) for actor in coalition)
        lhs = final_units * model.chi + join_res + SCALE * paid + exit_res
        rhs = initial_units * initial_chi + acc + SCALE * joined
        require(lhs == rhs, f"trial {trial}: coalition telescope failed")
        require(model.Pie == sum(model.rows.values()),
                f"trial {trial}: Pie/row conservation failed")
        require(model.balance + total_paid ==
                int(initial["balance"]) + total_join + outside,
                f"trial {trial}: balance telescope failed")
        checks += 3
    return checks


def self_test(root: dict[str, Any]) -> int:
    mutations: list[tuple[str, Callable[[dict[str, Any]], None]]] = [
        ("drop-obligation", lambda value: value["scenarioObligations"].pop()),
        ("change-k3-factor", lambda value: value["factorVectors"][3].__setitem__(
            "factor", value["factorVectors"][3]["factor"] + 1)),
        ("hide-underfunded-revert", lambda value: value["transcripts"]
            ["failureAndReentry"][0].__setitem__("status", "success")),
        ("drop-initial-entitlement", lambda value: value["accountingVector"]
            ["terms"].__setitem__("initialUnitsTimesChi", 0)),
        ("change-segment-spread", lambda value: value["segmentVectors"].__setitem__(
            "spread", 0)),
        ("float-laundering", lambda value: value["constants"].__setitem__("S", float(SCALE))),
    ]
    for name, mutate in mutations:
        candidate = copy.deepcopy(root)
        mutate(candidate)
        try:
            validate_vectors(candidate)
        except CheckError:
            continue
        raise CheckError(f"self-test mutation escaped: {name}")
    return len(mutations)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    try:
        root = load_vectors()
        validate_vectors(root)
        if args.self_test:
            count = self_test(root)
            print(f"OK — DRIP oracle self-test: {count}/{count} corruptions rejected")
            return 0
        arithmetic = check_arithmetic_semantics()
        state = check_state_semantics()
        accounting = check_random_accounting()
        print(
            "OK — DRIP oracle semantics: 38 obligations; "
            f"{arithmetic} arithmetic, {state} state, {accounting} accounting checks"
        )
        return 0
    except (CheckError, Revert) as error:
        print(f"REGRESSION — DRIP oracle: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
