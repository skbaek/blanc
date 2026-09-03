#!/usr/bin/env python3
"""Check the independent PRORATA WETH vault oracle against the frozen statement.

The oracle in `prorata_weth_vault_oracle.py` is written from
`~/plans/reports/prorata-erc4626-port-sf.md` §4 rather than from the Lean
development.  This gate checks the properties the SF *asserts* about those
formulas, so that a transcription error in either the oracle or the statement
shows up here rather than in a differential run.

It is evidence, not a theorem: nothing checked here is reflected into Lean.
"""
from __future__ import annotations

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import prorata_weth_vault_oracle as V

FAILURES: list[str] = []


def fail(msg: str) -> None:
    FAILURES.append(msg)


def states():
    """Boundary and interior states, including the `A = U` case."""
    assets = [0, 1, 2, 1000, 10 ** 18, 2 ** 128, 2 ** 255, V.U - 1, V.U]
    supplies = [0, 1, 1000, 10 ** 18, 2 ** 128, V.MAX_SUPPLY - 1, V.MAX_SUPPLY]
    for a in assets:
        for s in supplies:
            yield a, s



def funded(*holders: int) -> V.Vault:
    """A vault whose holders hold WETH and have approved the vault for it."""
    v = V.Vault(weth={h: 10 ** 30 for h in holders})
    v.weth_allowances = {(h, v.vault_address): V.U for h in holders}
    return v


def check_representability_identity() -> None:
    """SF: `ceil(s*X/D) <= U` exactly when `s <= floor(U*D/X)`."""
    for A, S in states():
        X, D = V.numerator(A), V.denominator(S)
        cap = V.floor_div(V.U * D, X)
        for s in {0, 1, max(cap - 1, 0), cap, cap + 1}:
            lhs = V.ceil_div(s * X, D) <= V.U
            if lhs != (s <= cap):
                fail(f"representability identity at A={A} S={S} s={s}")
                return


def check_max_mint_tight() -> None:
    """`maxMint` is the largest `s` that fits supply room and is representable."""
    for A, S in states():
        m = V.max_mint(1, A, S)
        if m > V.share_room(S):
            fail(f"maxMint exceeds share room at A={A} S={S}")
            return
        try:
            V.preview_mint(m, A, S)
        except V.Revert:
            fail(f"maxMint not representable at A={A} S={S}")
            return
        nxt = m + 1
        fits = nxt <= V.share_room(S)
        try:
            V.preview_mint(nxt, A, S)
            representable = True
        except V.Revert:
            representable = False
        if fits and representable:
            fail(f"maxMint not maximal at A={A} S={S}: {nxt} also admissible")
            return


def check_max_deposit_tight() -> None:
    """SF: `maxDeposit` is the largest word `a` with `floor(a*D/X) <= shareRoom`."""
    for A, S in states():
        m = V.max_deposit(1, A, S)
        X, D = V.numerator(A), V.denominator(S)
        if m > 0 and V.floor_div(m * D, X) > V.share_room(S):
            fail(f"maxDeposit admits more shares than the room at A={A} S={S}")
            return
        if m < V.U and V.floor_div((m + 1) * D, X) <= V.share_room(S):
            fail(f"maxDeposit not maximal at A={A} S={S}")
            return


def check_zero_receiver_capacity() -> None:
    """SF: the zero receiver reports zero capacity (registered deviation 3)."""
    for A, S in states():
        if V.max_mint(0, A, S) != 0 or V.max_deposit(0, A, S) != 0:
            fail(f"zero receiver reports capacity at A={A} S={S}")
            return


def check_rounding_directions() -> None:
    """Each preview rounds in the direction the SF's table names."""
    rng = random.Random(20260904)
    for A, S in states():
        X, D = V.numerator(A), V.denominator(S)
        for _ in range(8):
            v = rng.randrange(0, 1 << rng.choice([1, 8, 64, 200]))
            try:
                if V.convert_to_shares(v, A, S) * X > v * D:
                    fail(f"convertToShares rounded up at A={A} S={S} v={v}")
                    return
                if V.convert_to_assets(v, A, S) * D > v * X:
                    fail(f"convertToAssets rounded up at A={A} S={S} v={v}")
                    return
                if V.preview_mint(v, A, S) * D < v * X:
                    fail(f"previewMint rounded down at A={A} S={S} v={v}")
                    return
                if V.preview_withdraw(v, A, S) * X < v * D:
                    fail(f"previewWithdraw rounded down at A={A} S={S} v={v}")
                    return
            except V.Revert:
                continue


def check_rounding_favours_the_vault() -> None:
    """A round trip never returns more than it took in.

    This is the property the virtual offset exists to protect, stated over the
    conversion formulas alone.
    """
    rng = random.Random(4626)
    for A, S in states():
        for _ in range(8):
            a = rng.randrange(0, 1 << rng.choice([1, 8, 64, 128]))
            try:
                shares = V.convert_to_shares(a, A, S)
                back = V.convert_to_assets(shares, A, S)
            except V.Revert:
                continue
            if back > a:
                fail(f"deposit/redeem round trip profits at A={A} S={S} a={a}")
                return


def check_conservation_over_transcripts() -> None:
    """Balances sum to supply after every step of a randomized transcript."""
    rng = random.Random(1000)
    for trial in range(200):
        v = funded(2, 3, 4)
        for _ in range(rng.randrange(1, 12)):
            who = rng.choice([2, 3, 4])
            op = rng.choice(["deposit", "mint", "withdraw", "redeem",
                             "transfer", "approve", "donate"])
            try:
                if op == "deposit":
                    v.deposit(who, rng.randrange(0, 10 ** 9), who)
                elif op == "mint":
                    v.mint(who, rng.randrange(0, 10 ** 9), who)
                elif op == "withdraw":
                    v.withdraw(who, rng.randrange(0, 10 ** 9), who, who)
                elif op == "redeem":
                    v.redeem(who, rng.randrange(0, 10 ** 9), who, who)
                elif op == "transfer":
                    v.transfer(who, rng.choice([2, 3, 4]), rng.randrange(0, 10 ** 9))
                elif op == "approve":
                    v.approve(who, rng.choice([2, 3, 4]), rng.randrange(0, 10 ** 9))
                else:
                    v.donate(who, rng.randrange(0, 10 ** 9))
            except V.Revert:
                pass
            if not v.conserved():
                fail(f"conservation broken in trial {trial} after {op}")
                return


def check_donation_mints_nothing() -> None:
    """A third-party WETH transfer to the vault is a donation, not a deposit."""
    v = funded(2, 3)
    v.deposit(2, 10 ** 6, 2)
    before_supply, before_balance = v.supply, v.balance_of(3)
    v.donate(3, 10 ** 9)
    if v.supply != before_supply or v.balance_of(3) != before_balance:
        fail("donation moved the share ledger")


def check_offset_bounds_the_first_depositor_attack() -> None:
    """The classic first-depositor inflation attack does not profit.

    The control is a self-contained *unoffset* ERC-4626 reference — the
    textbook `shares = assets` bootstrap and `a*S/A` thereafter — run on the
    identical transcript.  It must either profit the attacker or mint the
    victim nothing; if it does neither, this test is not testing the offset
    and says so.  The reference is written out here rather than obtained by
    setting `O = 0` in the oracle, because at `O = 0` and zero supply the
    oracle's denominator is zero: having no bootstrap case is precisely what
    the offset buys.
    """
    seed, donation, victim_assets = 1, 10 ** 6, 10 ** 6

    vault = funded(2, 3)
    vault.deposit(2, seed, 2)
    vault.donate(2, donation)
    victim_shares = vault.deposit(3, victim_assets, 3)
    attacker_out = vault.redeem(2, vault.balance_of(2), 2, 2)
    profit = attacker_out - (seed + donation)
    if profit > 0:
        fail(f"offset-live inflation attack profits by {profit}")
    if victim_shares == 0:
        fail("offset-live victim was minted nothing")

    supply, assets, shares = 0, 0, {}

    def ref_deposit(who: int, a: int) -> int:
        nonlocal supply, assets
        minted = a if supply == 0 else a * supply // assets
        shares[who] = shares.get(who, 0) + minted
        supply += minted
        assets += a
        return minted

    def ref_donate(a: int) -> None:
        nonlocal assets
        assets += a

    def ref_redeem(who: int, s: int) -> int:
        nonlocal supply, assets
        out = s * assets // supply
        shares[who] -= s
        supply -= s
        assets -= out
        return out

    ref_deposit(2, seed)
    ref_donate(donation)
    control_victim_shares = ref_deposit(3, victim_assets)
    control_out = ref_redeem(2, shares[2])
    control_profit = control_out - (seed + donation)
    if control_profit <= 0 and control_victim_shares != 0:
        fail("offset-disabled control does not bite: on the same transcript "
             f"the unoffset reference neither profits (profit="
             f"{control_profit}) nor starves the victim "
             f"(shares={control_victim_shares})")


CHECKS = [
    check_representability_identity,
    check_max_mint_tight,
    check_max_deposit_tight,
    check_zero_receiver_capacity,
    check_rounding_directions,
    check_rounding_favours_the_vault,
    check_conservation_over_transcripts,
    check_donation_mints_nothing,
    check_offset_bounds_the_first_depositor_attack,
]


def main() -> int:
    for check in CHECKS:
        check()
    if FAILURES:
        for message in FAILURES:
            print(f"REGRESSION — vault oracle: {message}")
        return 1
    print(f"OK — vault oracle: {len(CHECKS)} property batteries over "
          f"{len(list(states()))} boundary states agree with the frozen "
          f"statement; offset-disabled control bites")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
