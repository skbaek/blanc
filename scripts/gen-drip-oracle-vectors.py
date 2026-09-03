#!/usr/bin/env python3
"""Generate/check timing-free exact-integer DRIP oracle vectors.

Normal mode is read-only and byte-compares the committed JSON.  ``--write``
is the sole writer.  The vectors pin arithmetic and whole-message rollback;
they do not claim EVM execution or compiler-byte evidence.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Callable

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
OUT = ROOT / "scripts" / "drip-oracle-vectors.json"

ALICE = 0xA11CE
BOB = 0xB0B
CAROL = 0xCA201
YEAR = 31_536_000

OBLIGATIONS = (
    "deployment-genesis",
    "drip-same-timestamp",
    "drip-local-under-k2",
    "drip-local-over-k3",
    "drip-one-year",
    "drip-max-elapsed",
    "drip-elapsed-overflow-revert",
    "drip-timestamp-regression-revert",
    "drip-chi-below-scale-revert",
    "drip-chi-above-cap-revert",
    "drip-post-chi-cap-boundary",
    "drip-post-chi-cap-revert",
    "join-zero-value",
    "join-genesis-first",
    "join-future-auto-drip",
    "join-max-asset",
    "join-over-max-asset-revert",
    "join-total-or-row-cap-revert",
    "join-zero-unit-credit",
    "exit-zero-unit-call",
    "exit-partial",
    "exit-full",
    "exit-future-auto-drip",
    "exit-insufficient-units-revert",
    "exit-underfunded-call-rollback",
    "exit-rejecting-recipient-rollback",
    "exit-successful-reentry",
    "view-units-fresh-consistency",
    "view-assets-fresh-consistency",
    "view-arithmetic-cap-boundaries",
    "receive-value-donation",
    "receive-zero-value",
    "unknown-selector-revert",
    "short-and-trailing-calldata-revert",
    "value-bearing-nonpayable-revert",
    "multi-participant-conservation",
    "segmentation-k3-versus-k1-k2",
    "receipt-returndata-log-matrix",
)


def expect(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def attempt(model: Drip, label: str, action: Callable[[], int | None]) -> dict[str, object]:
    pre = model.snapshot()
    try:
        result = action()
    except Revert as error:
        post = model.snapshot()
        expect(post == pre, f"{label}: reverting call changed state")
        return {
            "label": label,
            "status": "revert",
            "reason": error.reason,
            "pre": pre,
            "post": post,
        }
    return {
        "label": label,
        "status": "success",
        "result": result,
        "pre": pre,
        "post": model.snapshot(),
    }


def factor_vectors() -> list[dict[str, object]]:
    rows = []
    for elapsed in (0, 1, 2, 3, YEAR, MAX_ELAPSED):
        factor, steps = rpow_checked(RATE, elapsed)
        rows.append({
            "elapsed": elapsed,
            "factor": factor,
            "operationCount": len(steps),
            "operationKinds": [step.kind for step in steps],
            "largestProduct": max((step.product for step in steps), default=0),
        })

    by_elapsed = {row["elapsed"]: row for row in rows}
    expect(by_elapsed[2]["factor"] == 1_000_000_003_094_251_918_120_023_625,
           "k=2 factor drift")
    expect(by_elapsed[3]["factor"] == 1_000_000_004_641_377_880_770_433_536,
           "k=3 factor drift")
    expect(by_elapsed[YEAR]["factor"] == 1_049_999_999_999_999_999_961_070_145,
           "one-year factor drift")
    expect(by_elapsed[MAX_ELAPSED]["factor"] ==
           768_818_856_951_536_117_615_218_517_260,
           "maximum-elapsed factor drift")
    expect(by_elapsed[MAX_ELAPSED]["operationCount"] == 62,
           "maximum-elapsed operation count drift")
    for row in rows:
        expect(row["operationCount"] == operation_count(int(row["elapsed"])),
               f"operation formula drift at {row['elapsed']}")
    return rows


def rounding_witnesses() -> dict[str, object]:
    _, steps_two = rpow_checked(RATE, 2)
    _, steps_three = rpow_checked(RATE, 3)
    first_square = steps_two[0]
    multiply = next(step for step in steps_three if step.kind == "multiply")
    square_error = SCALE * first_square.result - first_square.product
    multiply_error = SCALE * multiply.result - multiply.product
    expect(square_error == -494_162_619_157_761_202_382_152_704,
           "local under witness drift")
    expect(multiply_error == 308_476_035_340_184_723_845_916_000,
           "local over witness drift")
    return {
        "under": {"elapsed": 2, "kind": "square", "scaledError": square_error},
        "over": {"elapsed": 3, "kind": "multiply", "scaledError": multiply_error},
    }


def guard_vectors() -> dict[str, object]:
    max_factor, _ = rpow_checked(RATE, MAX_ELAPSED)
    accepted = ((MAX_CHI + 1) * SCALE - 1) // max_factor
    accepted_fresh = fresh_index(accepted, 0, MAX_ELAPSED)
    expect(accepted == 442_604_085_272_050_989_502_489_636_102_618_752,
           "last accepted chi drift")
    expect(accepted_fresh.value ==
           340_282_366_920_938_463_463_374_607_431_768_211_167,
           "accepted boundary output drift")
    try:
        fresh_index(accepted + 1, 0, MAX_ELAPSED)
    except Revert as error:
        rejected_reason = error.reason
    else:
        raise AssertionError("post-chi cap boundary stopped reverting")
    expect(rejected_reason == "fresh-chi-over-cap", "wrong boundary guard")
    return {
        "lastAcceptedChi": accepted,
        "lastAcceptedFreshChi": accepted_fresh.value,
        "firstRejectedChi": accepted + 1,
        "firstRejectedMathematicalFreshChi":
            (accepted + 1) * max_factor // SCALE,
        "firstRejectedReason": rejected_reason,
        "maxAssetScaleBits": (MAX_ASSET * SCALE).bit_length(),
        "maxUnitsChiBits": (MAX_UNITS * MAX_CHI).bit_length(),
    }


def surface_vectors() -> list[dict[str, int]]:
    rows = []
    for chi, assets, units in (
        (SCALE, 0, 0),
        (SCALE, 1, 1),
        (SCALE + 1, 1, 1),
        (1_049_999_999_999_999_999_961_070_145, SCALE, SCALE),
        (MAX_CHI, MAX_ASSET, MAX_UNITS),
    ):
        minted = units_for_assets(assets, chi)
        payout = assets_for_units(units, chi)
        jr = join_residue(assets, minted, chi)
        er = exit_residue(units, payout, chi)
        expect(0 <= jr < chi, "join residue outside divisor")
        expect(0 <= er < SCALE, "exit residue outside scale")
        rows.append({
            "chi": chi,
            "assets": assets,
            "mintedUnits": minted,
            "joinResidue": jr,
            "units": units,
            "payoutAssets": payout,
            "exitResidue": er,
        })
    return rows


def transcript_vectors() -> dict[str, object]:
    model = Drip(100)
    rows = [
        attempt(model, "join-genesis-first", lambda: model.join(ALICE, 10**27, 100)),
        attempt(model, "receive-value-donation", lambda: model.receive(17)),
        attempt(model, "drip-local-over-k3", lambda: model.drip(103)),
        attempt(model, "join-future-auto-drip", lambda: model.join(BOB, 10**18, 106)),
        attempt(model, "exit-partial", lambda: model.exit(ALICE, 10**18, 109)),
        attempt(model, "receive-zero-value", lambda: model.receive(0)),
    ]
    expect(model.Pie == sum(model.rows.values()), "transcript ledger conservation")

    zero_call_count = 0

    def accept_zero(_model: Drip, payout: int) -> bool:
        nonlocal zero_call_count
        expect(payout == 0, "zero-unit exit paid nonzero")
        zero_call_count += 1
        return True

    rows.append(attempt(
        model, "exit-zero-unit-call",
        lambda: model.exit(ALICE, 0, 109, accept_zero),
    ))
    expect(zero_call_count == 1, "zero-unit exit skipped recipient CALL")

    failed = Drip(0)
    failed.join(ALICE, 100, 0)
    underfunded = attempt(
        failed, "exit-underfunded-call-rollback",
        lambda: failed.exit(ALICE, 100, YEAR),
    )
    expect(underfunded["status"] == "revert" and
           underfunded["reason"] == "outbound-call-failed",
           "underfunded CALL control stopped reverting at the CALL boundary")
    rows.append(underfunded)

    rejected = Drip(0)
    rejected.join(ALICE, 10**18, 0)

    def reject_after_nested(current: Drip, _payout: int) -> bool:
        current.join(BOB, 123, 3)
        return False

    rejected_result = attempt(
        rejected, "exit-rejecting-recipient-rollback",
        lambda: rejected.exit(ALICE, 1, 3, reject_after_nested),
    )
    expect(rejected_result["status"] == "revert" and
           rejected_result["reason"] == "outbound-call-failed",
           "rejecting-recipient control stopped reverting")
    rows.append(rejected_result)
    expect(rejected.row(BOB) == 0, "failed outer exit retained nested write")

    reentrant = Drip(0)
    reentrant.join(ALICE, 10**24, 0)

    def successful_reentry(current: Drip, payout: int) -> bool:
        expect(current.row(ALICE) == 10**24 - 1, "outer debit not visible to callback")
        current.join(CAROL, payout + 1, 3)
        return True

    reentry_result = attempt(
        reentrant, "exit-successful-reentry",
        lambda: reentrant.exit(ALICE, 1, 3, successful_reentry),
    )
    expect(reentry_result["status"] == "success",
           "successful reentry control stopped committing")
    rows.append(reentry_result)
    expect(reentrant.row(CAROL) > 0, "successful nested join did not commit")
    expect(reentrant.Pie == sum(reentrant.rows.values()), "reentrant ledger conservation")

    return {
        "ordinary": rows[:7],
        "failureAndReentry": rows[7:],
        "ordinaryFinal": model.snapshot(),
        "underfundedFinal": failed.snapshot(),
        "reentrantFinal": reentrant.snapshot(),
        "zeroUnitRecipientCalls": zero_call_count,
    }


def view_vectors() -> dict[str, object]:
    model = Drip(1_000)
    before = model.snapshot()
    units = model.convert_to_units(10**24, 1_003)
    assets = model.convert_to_assets(10**24, 1_003)
    expect(model.snapshot() == before, "views changed state")

    joined = Drip(1_000)
    join_result = joined.join(ALICE, 10**24, 1_003)
    expect(join_result == units, "fresh unit view differs from same-state join")
    exited = Drip(1_000)
    exited.join(ALICE, 10**24, 1_000)
    exit_view = exited.convert_to_assets(1, 1_003)
    exit_result = exited.exit(ALICE, 1, 1_003)
    expect(exit_result == exit_view, "fresh asset view differs from successful exit")
    return {
        "timestamp": 1_003,
        "unitPreview": units,
        "assetPreview": assets,
        "sameStateJoinResult": join_result,
        "sameStateExitPreview": exit_view,
        "sameStateExitResult": exit_result,
        "viewStatePreserved": True,
    }


def boundary_call_vectors() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []

    elapsed = Drip(0)
    rows.append(attempt(
        elapsed, "drip-elapsed-overflow-revert",
        lambda: elapsed.drip(MAX_ELAPSED + 1),
    ))

    regressed = Drip(10)
    rows.append(attempt(
        regressed, "drip-timestamp-regression-revert",
        lambda: regressed.drip(9),
    ))

    low_chi = Drip(0)
    low_chi.chi = SCALE - 1
    rows.append(attempt(
        low_chi, "drip-chi-below-scale-revert", lambda: low_chi.drip(0),
    ))

    high_chi = Drip(0)
    high_chi.chi = MAX_CHI + 1
    rows.append(attempt(
        high_chi, "drip-chi-above-cap-revert", lambda: high_chi.drip(0),
    ))

    max_factor, _ = rpow_checked(RATE, MAX_ELAPSED)
    last_chi = ((MAX_CHI + 1) * SCALE - 1) // max_factor
    cap_boundary = Drip(0)
    cap_boundary.chi = last_chi
    rows.append(attempt(
        cap_boundary, "drip-post-chi-cap-boundary",
        lambda: cap_boundary.drip(MAX_ELAPSED),
    ))
    cap_revert = Drip(0)
    cap_revert.chi = last_chi + 1
    rows.append(attempt(
        cap_revert, "drip-post-chi-cap-revert",
        lambda: cap_revert.drip(MAX_ELAPSED),
    ))

    maximum_join = Drip(0)
    rows.append(attempt(
        maximum_join, "join-max-asset",
        lambda: maximum_join.join(ALICE, MAX_ASSET, 0),
    ))
    over_asset = Drip(0)
    rows.append(attempt(
        over_asset, "join-over-max-asset-revert",
        lambda: over_asset.join(ALICE, MAX_ASSET + 1, 0),
    ))

    full_row = Drip(0)
    full_row.rows[ALICE] = MAX_UNITS
    full_row.Pie = MAX_PIE
    rows.append(attempt(
        full_row, "join-total-or-row-cap-revert",
        lambda: full_row.join(ALICE, 1, 0),
    ))

    zero_units = Drip(0)
    zero_units.chi = MAX_CHI
    rows.append(attempt(
        zero_units, "join-zero-unit-credit",
        lambda: zero_units.join(ALICE, 1, 0),
    ))

    insufficient = Drip(0)
    insufficient.join(ALICE, 1, 0)
    rows.append(attempt(
        insufficient, "exit-insufficient-units-revert",
        lambda: insufficient.exit(ALICE, 2, 0),
    ))

    expected = {
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
    for row in rows:
        status, reason = expected[str(row["label"])]
        expect(row["status"] == status, f"{row['label']}: wrong status")
        if reason is not None:
            expect(row["reason"] == reason, f"{row['label']}: wrong guard precedence")
    zero_row = next(row for row in rows if row["label"] == "join-zero-unit-credit")
    expect(zero_row["result"] == 0 and
           zero_row["post"]["balance"] == zero_row["pre"]["balance"] + 1,
           "zero-unit join did not retain its credited asset")
    return rows


def accounting_vector() -> dict[str, object]:
    coalition = {ALICE, CAROL}
    model = Drip(0)
    model.join(ALICE, 10**24, 0)
    initial = model.snapshot()
    initial_units = model.row(ALICE) + model.row(CAROL)
    initial_chi = model.chi

    coalition_accrual = 0
    coalition_join = 0
    coalition_paid = 0
    coalition_join_residue = 0
    coalition_exit_residue = 0
    total_join = 0
    total_paid = 0
    outside_credit = 0
    steps: list[dict[str, object]] = []

    def coalition_units() -> int:
        return sum(model.row(address) for address in coalition)

    def accrue_term(pre: dict[str, object]) -> None:
        nonlocal coalition_accrual
        pre_rows = pre["rows"]
        pre_units = sum(
            int(pre_rows.get(f"0x{address:040x}", 0))
            for address in coalition
        )
        coalition_accrual += pre_units * (model.chi - int(pre["chi"]))

    def add_drip(now: int) -> None:
        pre = model.snapshot()
        value = model.drip(now)
        accrue_term(pre)
        steps.append({"kind": "drip", "now": now, "result": value})

    def add_join(caller: int, assets: int, now: int) -> None:
        nonlocal coalition_join, coalition_join_residue, total_join
        pre = model.snapshot()
        units = model.join(caller, assets, now)
        accrue_term(pre)
        total_join += assets
        if caller in coalition:
            coalition_join += assets
            coalition_join_residue += join_residue(assets, units, model.chi)
        steps.append({
            "kind": "join", "caller": f"0x{caller:040x}", "now": now,
            "assets": assets, "units": units,
        })

    def add_exit(caller: int, units: int, now: int) -> None:
        nonlocal coalition_paid, coalition_exit_residue, total_paid
        pre = model.snapshot()
        payout = model.exit(caller, units, now)
        accrue_term(pre)
        total_paid += payout
        if caller in coalition:
            coalition_paid += payout
            coalition_exit_residue += exit_residue(units, payout, model.chi)
        steps.append({
            "kind": "exit", "caller": f"0x{caller:040x}", "now": now,
            "units": units, "payout": payout,
        })

    def add_credit(amount: int) -> None:
        nonlocal outside_credit
        model.external_credit(amount)
        outside_credit += amount
        steps.append({"kind": "externalCredit", "amount": amount})

    add_drip(2)
    add_join(BOB, 3 * 10**23, 3)
    add_join(CAROL, 2 * 10**23, 3)
    add_credit(10**27)
    add_exit(ALICE, 10**20, 5)
    add_exit(CAROL, model.row(CAROL) // 3, 5)

    final_units = coalition_units()
    lhs = (
        final_units * model.chi
        + coalition_join_residue
        + SCALE * coalition_paid
        + coalition_exit_residue
    )
    rhs = (
        initial_units * initial_chi
        + coalition_accrual
        + SCALE * coalition_join
    )
    expect(lhs == rhs, "coalition accounting equality failed")
    expect(model.Pie == sum(model.rows.values()), "accounting ledger conservation failed")
    expect(model.balance + total_paid ==
           int(initial["balance"]) + total_join + outside_credit,
           "target-balance telescope failed")
    return {
        "coalition": [f"0x{address:040x}" for address in sorted(coalition)],
        "initial": initial,
        "final": model.snapshot(),
        "steps": steps,
        "terms": {
            "initialUnitsTimesChi": initial_units * initial_chi,
            "accrual": coalition_accrual,
            "joinAssets": coalition_join,
            "joinResidue": coalition_join_residue,
            "paidAssets": coalition_paid,
            "exitResidue": coalition_exit_residue,
            "finalUnitsTimesChi": final_units * model.chi,
            "lhs": lhs,
            "rhs": rhs,
            "outsideCredit": outside_credit,
        },
    }


def segment_vectors() -> dict[str, object]:
    single = segment_index(SCALE, (3,))
    split = segment_index(SCALE, (1, 2))
    spread = abs(single - split)
    expect(spread == 1, "frozen segmentation witness drift")
    return {
        "initialChi": SCALE,
        "singleParts": [3],
        "splitParts": [1, 2],
        "singleIndex": single,
        "splitIndex": split,
        "spread": spread,
        "certifiedBound": 4,
    }


def mutation_controls() -> dict[str, bool]:
    factor_three, _ = rpow_checked(RATE, 3)
    floor_square = RATE * RATE // SCALE
    floor_factor_three = RATE * floor_square // SCALE
    fresh = fresh_index(SCALE, 0, YEAR).value
    return {
        "halfUpDiffersFromFloor": floor_factor_three != factor_three,
        "segmentCompositionDiffersFromHalfUp":
            RATE * rpow_checked(RATE, 2)[0] // SCALE
            != (RATE * rpow_checked(RATE, 2)[0] + HALF) // SCALE,
        "autoDripChangesJoin":
            units_for_assets(SCALE, SCALE) != units_for_assets(SCALE, fresh),
        "joinFloorDiffersFromCeiling":
            units_for_assets(1, SCALE + 1) != (SCALE + (SCALE + 1) - 1) // (SCALE + 1),
        "exitFloorDiffersFromCeiling":
            assets_for_units(1, SCALE + 1) != ((SCALE + 1) + SCALE - 1) // SCALE,
        "k3FactorNontrivial": factor_three != SCALE,
    }


def build() -> bytes:
    controls = mutation_controls()
    expect(all(controls.values()), "one or more arithmetic mutation controls stopped biting")
    expect(len(OBLIGATIONS) == 38 and len(set(OBLIGATIONS)) == 38,
           "frozen scenario obligation inventory drift")
    expect(len({CHI_SLOT, RHO_SLOT, PIE_SLOT}) == 3, "scalar slots collide")
    expect(min(CHI_SLOT, RHO_SLOT, PIE_SLOT) > ADDRESS_MAX,
           "scalar slot entered address row space")
    expect(MAX_CHI == MAX_ASSET == MAX_UNITS == MAX_PIE,
           "symmetric cap drift")
    expect(MAX_UNITS * MAX_CHI < WORD_MODULUS, "frozen unit/index product no longer safe")

    obj = {
        "meta": {
            "schema": 1,
            "generator": "scripts/gen-drip-oracle-vectors.py",
            "model": "scripts/drip_oracle.py",
            "arithmetic": "unbounded Python integers plus explicit 256-bit guards",
            "claimBoundary": "falsifier and fixture oracle; not Lean or EVM proof evidence",
        },
        "constants": {
            "S": SCALE,
            "R": RATE,
            "H": HALF,
            "maxElapsed": MAX_ELAPSED,
            "maxChi": MAX_CHI,
            "maxAsset": MAX_ASSET,
            "maxUnits": MAX_UNITS,
            "maxPie": MAX_PIE,
            "chiSlot": CHI_SLOT,
            "rhoSlot": RHO_SLOT,
            "PieSlot": PIE_SLOT,
        },
        "scenarioObligations": list(OBLIGATIONS),
        "factorVectors": factor_vectors(),
        "roundingWitnesses": rounding_witnesses(),
        "guardVectors": guard_vectors(),
        "surfaceVectors": surface_vectors(),
        "viewVectors": view_vectors(),
        "boundaryCallVectors": boundary_call_vectors(),
        "accountingVector": accounting_vector(),
        "segmentVectors": segment_vectors(),
        "transcripts": transcript_vectors(),
        "mutationControls": controls,
    }
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true",
                        help="replace the sole generated output after all assertions pass")
    args = parser.parse_args()
    data = build()
    if args.write:
        OUT.write_bytes(data)
        print(f"OK — wrote {OUT.relative_to(ROOT)} ({len(data)} bytes; 38 obligations)")
        return
    if not OUT.is_file() or OUT.read_bytes() != data:
        raise SystemExit(
            "REGRESSION — DRIP oracle vectors are missing or stale; "
            "regenerate deliberately with --write"
        )
    print(
        "OK — DRIP oracle vectors match regeneration byte-for-byte "
        f"({len(data)} bytes; 38 obligations)"
    )


if __name__ == "__main__":
    main()
