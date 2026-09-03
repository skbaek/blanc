#!/usr/bin/env python3
"""Write/check the PRORATA WETH vault's golden oracle vectors.

The committed JSON is generated only by this script from
`prorata_weth_vault_oracle.py`, which is itself written from the frozen
statement rather than from the Lean development.  ``--check`` regenerates the
same canonical bytes and fails on drift.

The rows follow the SF §11 differential matrix as far as an arithmetic model
can carry it: empty, nonempty and donated states; every view and every
mutation; boundary rounding; the configured magnitude guards; failures and
rollback; and the frozen attack transcript.  Rows that need real EVM execution
-- events at the runner's altitude, malformed calldata, gas -- are not
simulated here and are left to the fixture harness, because a model that
pretended to cover them would be worse than one that does not.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import prorata_weth_vault_oracle as V

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "scripts" / "prorata-weth-vault-oracle-vectors.json"

VAULT = 1
ALICE, BOB = 2, 3


def funded() -> V.Vault:
    v = V.Vault(weth={ALICE: 10 ** 30, BOB: 10 ** 30})
    v.weth_allowances = {(ALICE, VAULT): V.U, (BOB, VAULT): V.U}
    return v


def views(assets: int, supply: int, holder_balance: int) -> dict:
    """Every view at one state, with reverts recorded rather than raised."""
    def guarded(fn, *args):
        try:
            return fn(*args)
        except V.Revert as exc:
            return {"revert": exc.cls}

    return {
        "totalAssets": assets,
        "totalSupply": supply,
        "convertToShares_1e18": guarded(V.convert_to_shares, 10 ** 18, assets, supply),
        "convertToAssets_1e18": guarded(V.convert_to_assets, 10 ** 18, assets, supply),
        "previewDeposit_1e18": guarded(V.preview_deposit, 10 ** 18, assets, supply),
        "previewMint_1e18": guarded(V.preview_mint, 10 ** 18, assets, supply),
        "previewWithdraw_1e18": guarded(V.preview_withdraw, 10 ** 18, assets, supply),
        "previewRedeem_1e18": guarded(V.preview_redeem, 10 ** 18, assets, supply),
        "maxDeposit_nonzero": V.max_deposit(ALICE, assets, supply),
        "maxDeposit_zero": V.max_deposit(0, assets, supply),
        "maxMint_nonzero": V.max_mint(ALICE, assets, supply),
        "maxMint_zero": V.max_mint(0, assets, supply),
        "maxWithdraw": V.max_withdraw(holder_balance, assets, supply),
        "maxRedeem": V.max_redeem(holder_balance),
    }


def state_rows() -> list:
    """Views at the three states the matrix names, plus the word ceiling."""
    rows = []
    for name, assets, supply, balance in [
        ("empty", 0, 0, 0),
        ("nonempty", 10 ** 18, 10 ** 21, 10 ** 20),
        ("donated", 3 * 10 ** 18, 10 ** 21, 10 ** 20),
        ("assets_at_word_ceiling", V.U, 10 ** 21, 10 ** 20),
        ("supply_at_cap", 10 ** 18, V.MAX_SUPPLY, 10 ** 20),
    ]:
        rows.append({"state": name, "views": views(assets, supply, balance)})
    return rows


def rounding_rows() -> list:
    """Boundary rounding: inputs straddling an exact division."""
    rows = []
    assets, supply = 3, 7000
    for a in range(0, 9):
        rows.append({
            "assets": assets, "supply": supply, "input": a,
            "convertToShares": V.convert_to_shares(a, assets, supply),
            "previewWithdraw": V.preview_withdraw(a, assets, supply),
            "convertToAssets": V.convert_to_assets(a, assets, supply),
            "previewMint": V.preview_mint(a, assets, supply),
        })
    return rows


def guard_rows() -> list:
    """The configured magnitude guards, at and just past their boundary."""
    rows = []
    assets, supply = 10 ** 18, 10 ** 21
    room = V.share_room(supply)
    cap_mint = V.max_mint(ALICE, assets, supply)
    cap_deposit = V.max_deposit(ALICE, assets, supply)
    for name, fn, arg in [
        ("mint_at_cap", V.preview_mint, cap_mint),
        ("mint_past_cap", V.preview_mint, cap_mint + 1),
        ("deposit_at_cap", V.convert_to_shares, cap_deposit),
        ("deposit_past_cap", V.convert_to_shares, cap_deposit + 1),
    ]:
        try:
            value = fn(arg, assets, supply)
            # For a deposit the guard is on the shares the assets buy; for a
            # mint it is on the requested shares themselves.
            fits = (value if name.startswith("deposit") else arg) <= room
            rows.append({"case": name, "input": arg, "result": value,
                         "fits_share_room": fits})
        except V.Revert as exc:
            rows.append({"case": name, "input": arg, "revert": exc.cls})
    return rows


def failure_rows() -> list:
    """Every frozen revert class the model can reach, with rollback checked."""
    rows = []

    def attempt(name, fn):
        v = funded()
        v.deposit(ALICE, 10 ** 9, ALICE)
        before = (v.supply, dict(v.balances), dict(v.weth))
        try:
            fn(v)
            rows.append({"case": name, "reverted": False})
        except V.Revert as exc:
            after = (v.supply, dict(v.balances), dict(v.weth))
            rows.append({"case": name, "reverted": True, "class": exc.cls,
                         "rolled_back": before == after})

    attempt("deposit_zero_receiver", lambda v: v.deposit(ALICE, 1, 0))
    attempt("withdraw_zero_owner", lambda v: v.withdraw(ALICE, 1, ALICE, 0))
    attempt("redeem_insufficient_balance",
            lambda v: v.redeem(ALICE, v.balance_of(ALICE) + 1, ALICE, ALICE))
    attempt("transfer_insufficient_balance",
            lambda v: v.transfer(ALICE, BOB, v.balance_of(ALICE) + 1))
    attempt("transfer_from_no_allowance",
            lambda v: v.transfer_from(BOB, ALICE, BOB, 1))
    attempt("approve_zero_spender", lambda v: v.approve(ALICE, 0, 1))
    return rows


def mutation_rows() -> list:
    """Every mutation once, from a shared nonempty state."""
    rows = []
    for name, fn in [
        ("deposit", lambda v: v.deposit(ALICE, 10 ** 9, ALICE)),
        ("mint", lambda v: v.mint(ALICE, 10 ** 9, ALICE)),
        ("withdraw", lambda v: v.withdraw(ALICE, 10 ** 6, ALICE, ALICE)),
        ("redeem", lambda v: v.redeem(ALICE, 10 ** 6, ALICE, ALICE)),
        ("transfer", lambda v: v.transfer(ALICE, BOB, 10 ** 6)),
        ("approve", lambda v: v.approve(ALICE, BOB, 10 ** 6)),
        ("transfer_from", lambda v: (v.approve(ALICE, BOB, 10 ** 6),
                                     v.transfer_from(BOB, ALICE, BOB, 10 ** 6))[1]),
        ("donate", lambda v: v.donate(BOB, 10 ** 9)),
    ]:
        v = funded()
        v.deposit(ALICE, 10 ** 12, ALICE)
        pre = {"supply": v.supply, "assets": v.total_assets(),
               "alice": v.balance_of(ALICE), "bob": v.balance_of(BOB)}
        result = fn(v)
        rows.append({
            "mutation": name, "pre": pre, "result": result,
            "post": {"supply": v.supply, "assets": v.total_assets(),
                     "alice": v.balance_of(ALICE), "bob": v.balance_of(BOB)},
            "conserved": v.conserved(),
            "logs": [list(entry) for entry in v.logs],
        })
    return rows


def attack_row() -> dict:
    """The frozen first-depositor transcript, priced on both sides."""
    seed, donation, victim_assets = 1, 10 ** 6, 10 ** 6
    v = funded()
    v.deposit(ALICE, seed, ALICE)
    v.donate(ALICE, donation)
    victim_shares = v.deposit(BOB, victim_assets, BOB)
    attacker_out = v.redeem(ALICE, v.balance_of(ALICE), ALICE, ALICE)
    victim_out = v.redeem(BOB, v.balance_of(BOB), BOB, BOB)
    return {
        "transcript": [["deposit", "attacker", seed],
                       ["donate", "attacker", donation],
                       ["deposit", "victim", victim_assets],
                       ["redeem", "attacker", "all"],
                       ["redeem", "victim", "all"]],
        "attacker_in": seed + donation,
        "attacker_out": attacker_out,
        "attacker_profit": attacker_out - (seed + donation),
        "victim_minted": victim_shares,
        "victim_in": victim_assets,
        "victim_out": victim_out,
        "victim_loss": victim_assets - victim_out,
    }


def build() -> bytes:
    attack = attack_row()
    if attack["attacker_profit"] > 0:
        raise AssertionError("the frozen attack transcript profits under the "
                             "live offset; the vectors would be wrong")
    obj = {
        "meta": {
            "generator": "scripts/gen-prorata-weth-vault-vectors.py",
            "model": "scripts/prorata_weth_vault_oracle.py",
            "statement": "~/plans/reports/prorata-erc4626-port-sf.md §4",
            "arithmetic": "Python integers, floor and ceiling division only",
            "offset": V.O,
            "not_covered": ["events at the runner's altitude",
                            "malformed calldata", "gas"],
        },
        "states": state_rows(),
        "rounding": rounding_rows(),
        "guards": guard_rows(),
        "failures": failure_rows(),
        "mutations": mutation_rows(),
        "attack": attack,
    }
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="regenerate and fail on drift instead of writing")
    args = parser.parse_args(argv)
    payload = build()
    if args.check:
        if not OUT.exists():
            print(f"REGRESSION — vault vectors: {OUT} is missing")
            return 1
        if OUT.read_bytes() != payload:
            print("REGRESSION — vault vectors: committed bytes differ from "
                  "the regenerated ones")
            return 1
        print(f"OK — vault vectors: {OUT.name} matches the regenerated bytes")
        return 0
    OUT.write_bytes(payload)
    print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
