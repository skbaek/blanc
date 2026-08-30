#!/usr/bin/env python3
"""Independent exact-arithmetic oracle for the PRORATA pro-rata share ledger.

Pure Python 3, standard library only, exact integer arithmetic throughout.
There are NO floats anywhere in this file (or in the companion brute-force
harness); every quantity is a Python ``int`` and every division is floor
division ``//`` unless a formula is stated as an exact cross-multiplied
inequality.

This module is both importable (the exact model + property helpers) and a CLI.
It is the reference semantics; the brute-force harness
(``prorata_bruteforce.py``) inlines the same arithmetic for speed and then
re-checks every witness transcript through this class to guarantee fidelity.

--------------------------------------------------------------------------
Model summary (this module is the reference semantics; checked results are in
scripts/prorata-oracle-findings.md)
--------------------------------------------------------------------------
Parameters: offset O >= 1 (virtual shares), MAXA, MAXS, MAXB (guard caps).
State: S (total shares), B (contract ETH balance), ledger: addr -> shares.
Invariant asserted at all times: sum(ledger.values()) == S.

deposit(addr, a)  [payable, a = msg.value >= 0]:
    B_pre := B                         # balance BEFORE crediting a
    revert if a > MAXA
    revert if B_pre > MAXB             # post-review guard (matches contract): at
                                       # B_pre = 2^256-1 the EVM denominator
                                       # B_pre+1 wraps to 0 and a deposit would
                                       # mint 0 for nonzero value; the deployed
                                       # contract reverts such deposits instead
    m := a * (S + O) // (B_pre + 1)
    revert if S + m > MAXS
    ledger[addr] += m ; S += m ; B := B_pre + a ; return m

withdraw(addr, s) [nonpayable]:
    revert if s > ledger[addr]
    revert if B > MAXB
    p := s * (B + 1) // (S + O)
    assert p <= B                      # structural solvency of the outbound send
    ledger[addr] -= s ; S -= s ; B -= p ; return p    # checks-effects-interactions

donate(a):  B += a                     # mints nothing, cannot revert (models forced ETH)

Views (pure): convertToShares(a) mirrors deposit's m with B_pre = B (no incoming
value); convertToAssets(s) mirrors withdraw's p.  Views revert exactly on their
arithmetic guards (convertToShares: a>MAXA, B>MAXB, S+m>MAXS; convertToAssets:
B>MAXB, and — post-review, matching the deployed view's word-width bound on
s*(B+1) — s>MAXS); the ledger sufficiency check is NOT a view concern.  Note
the s>MAXS view guard cannot fire on a withdraw-reachable argument (a real
withdraw's s is bounded by the supply cap via the ledger: s <= ledger <= S <=
MAXS), so op/view revert agreement on the withdraw domain is unchanged.

Offset-DISABLED variant (classic vulnerable vault, anti-vacuity control):
    deposit m := a if S == 0 else a * S // B_pre
             (B_pre == 0 and S > 0: m := 0, flagged)
    withdraw p := s * B // S           (S > 0 guaranteed by s <= ledger)
    No virtual offset anywhere; same checks-effects-interactions ordering.
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Optional


# ---------------------------------------------------------------------------
# Default concrete constants (used by CLI and by concrete-parameter sweeps).
# ---------------------------------------------------------------------------
DEFAULT_O = 10 ** 3
DEFAULT_MAXA = 2 ** 96 - 1
DEFAULT_MAXS = 2 ** 126 - 1
DEFAULT_MAXB = 2 ** 126 - 1


class Revert(Exception):
    """Raised when an operation reverts; leaves model state unchanged."""

    def __init__(self, reason: str):
        super().__init__(reason)
        self.reason = reason


class ProRata:
    """Exact stateful model of the PRORATA ledger.

    ``offset_enabled=False`` selects the classic vulnerable (no-virtual-offset)
    variant used only as the anti-vacuity control.
    """

    def __init__(
        self,
        O: int = DEFAULT_O,
        MAXA: int = DEFAULT_MAXA,
        MAXS: int = DEFAULT_MAXS,
        MAXB: int = DEFAULT_MAXB,
        offset_enabled: bool = True,
    ):
        assert O >= 1, "offset O must be >= 1"
        self.O = O
        self.MAXA = MAXA
        self.MAXS = MAXS
        self.MAXB = MAXB
        self.offset_enabled = offset_enabled
        self.S = 0
        self.B = 0
        self.ledger: dict = {}
        # Non-fatal notes (e.g. the disabled-variant B_pre==0,S>0 degenerate case).
        self.flags: list = []
        self._assert_invariant()

    # -- invariant -----------------------------------------------------------
    def _assert_invariant(self) -> None:
        # The hard model-consistency invariant. A violation here is a model bug,
        # not a property finding, so it is a real assertion.
        assert sum(self.ledger.values()) == self.S, (
            f"ledger sum {sum(self.ledger.values())} != S {self.S}"
        )

    # -- mutating operations -------------------------------------------------
    def deposit(self, addr, a: int) -> int:
        assert a >= 0, "deposit value must be >= 0"
        B_pre = self.B
        S = self.S
        O = self.O
        if self.offset_enabled:
            if a > self.MAXA:
                raise Revert("deposit: a > MAXA")
            if B_pre > self.MAXB:
                # Post-review guard matching the contract: guards the EVM
                # denominator B_pre+1 against wrap-to-zero at 2^256-1.
                raise Revert("deposit: B_pre > MAXB")
            m = a * (S + O) // (B_pre + 1)
            if S + m > self.MAXS:
                raise Revert("deposit: S + m > MAXS")
        else:
            if a > self.MAXA:
                raise Revert("deposit: a > MAXA")
            if S == 0:
                m = a
            elif B_pre == 0:
                m = 0
                self.flags.append(("disabled_deposit_Bpre0_Spos", dict(S=S, a=a)))
            else:
                m = a * S // B_pre
            if S + m > self.MAXS:
                raise Revert("deposit: S + m > MAXS")
        # effects
        self.ledger[addr] = self.ledger.get(addr, 0) + m
        self.S = S + m
        self.B = B_pre + a
        self._assert_invariant()
        return m

    def withdraw(self, addr, s: int) -> int:
        if s > self.ledger.get(addr, 0):
            raise Revert("withdraw: s > ledger[addr]")
        if self.B > self.MAXB:
            raise Revert("withdraw: B > MAXB")
        S = self.S
        B = self.B
        O = self.O
        if self.offset_enabled:
            p = s * (B + 1) // (S + O)
        else:
            if S == 0:
                p = 0
            else:
                p = s * B // S
        # Structural solvency of the outbound send: believed always true; flag
        # loudly (never silently) if it is ever violated.
        if p > B:
            self.flags.append(("SOLVENCY_VIOLATION_p_gt_B",
                               dict(addr=addr, s=s, p=p, B=B, S=S, O=O,
                                    offset_enabled=self.offset_enabled)))
            raise Revert("withdraw: STRUCTURAL SOLVENCY VIOLATION p > B")
        # effects (checks-effects-interactions: state settles before the send)
        self.ledger[addr] -= s
        self.S = S - s
        self.B = B - p
        self._assert_invariant()
        return p

    def donate(self, a: int) -> None:
        assert a >= 0, "donate value must be >= 0"
        self.B += a
        # ledger/S untouched; invariant trivially preserved.

    # -- views (pure; do not mutate) ----------------------------------------
    def convertToShares(self, a: int) -> int:
        """Shares a deposit of ``a`` would mint at the current state (B_pre=B)."""
        assert a >= 0
        S, O, B = self.S, self.O, self.B
        if self.offset_enabled:
            if a > self.MAXA:
                raise Revert("convertToShares: a > MAXA")
            if B > self.MAXB:
                # Post-review guard matching deposit's new B_pre > MAXB guard,
                # keeping the view's revert region identical to deposit's
                # arithmetic region.
                raise Revert("convertToShares: B > MAXB")
            m = a * (S + O) // (B + 1)
            if S + m > self.MAXS:
                raise Revert("convertToShares: S + m > MAXS")
            return m
        # disabled-variant view for completeness (not exercised by P2)
        if a > self.MAXA:
            raise Revert("convertToShares: a > MAXA")
        if S == 0:
            m = a
        elif B == 0:
            m = 0
        else:
            m = a * S // B
        if S + m > self.MAXS:
            raise Revert("convertToShares: S + m > MAXS")
        return m

    def convertToAssets(self, s: int) -> int:
        """Assets a withdrawal of ``s`` shares would pay at the current state.

        No ledger requirement: ``s`` is hypothetical. Reverts on B > MAXB and
        (post-review, offset-enabled path; order irrelevant, all-or-nothing) on
        s > MAXS — the word-width bound on s*(B+1) in the deployed view. On the
        withdraw-reachable domain (s <= ledger <= S <= MAXS) the s > MAXS guard
        never fires, so nothing changes for op/view agreement there.
        """
        S, O, B = self.S, self.O, self.B
        if B > self.MAXB:
            raise Revert("convertToAssets: B > MAXB")
        if self.offset_enabled:
            if s > self.MAXS:
                raise Revert("convertToAssets: s > MAXS")
            return s * (B + 1) // (S + O)
        if S == 0:
            return 0
        return s * B // S

    # -- utilities -----------------------------------------------------------
    def snapshot(self) -> dict:
        return dict(S=self.S, B=self.B, ledger=dict(self.ledger),
                    O=self.O, offset_enabled=self.offset_enabled)


# ---------------------------------------------------------------------------
# Pure property helpers (exact; return list of violation dicts, empty == pass).
# These operate on pre-state values so the harness can call them uniformly.
# ---------------------------------------------------------------------------
def deposit_property_violations(pre_S, pre_B, O, a, m):
    """P1/P3 checks for a single deposit. ``pre_B`` is B_pre (pre-credit)."""
    v = []
    B_pre = pre_B
    # P1: never over-mints
    if not (m * (B_pre + 1) <= a * (pre_S + O)):
        v.append(("P1_deposit_overmint",
                  dict(pre_S=pre_S, B_pre=B_pre, O=O, a=a, m=m)))
    # P1: cross-multiplied price monotonicity across the deposit
    #   (B_pre + a + 1)*(S + O) >= (B_pre + 1)*(S + m + O)
    lhs = (B_pre + a + 1) * (pre_S + O)
    rhs = (B_pre + 1) * (pre_S + m + O)
    if not (lhs >= rhs):
        v.append(("P1_deposit_price_monotone",
                  dict(pre_S=pre_S, B_pre=B_pre, O=O, a=a, m=m,
                       lhs=lhs, rhs=rhs)))
    # P3(c): exact residue  a*(S+O) = m*(B_pre+1) + r , 0 <= r <= B_pre
    r = a * (pre_S + O) - m * (B_pre + 1)
    if not (0 <= r <= B_pre):
        v.append(("P3c_deposit_residue",
                  dict(pre_S=pre_S, B_pre=B_pre, O=O, a=a, m=m, r=r)))
    return v


def withdraw_property_violations(pre_S, pre_B, O, s, p):
    """P1/P3 checks for a single withdraw."""
    v = []
    B = pre_B
    S = pre_S
    # P1: pays out no more than proportional
    if not (p * (S + O) <= s * (B + 1)):
        v.append(("P1_withdraw_overpay",
                  dict(pre_S=S, pre_B=B, O=O, s=s, p=p)))
    # P1: price non-decreasing across the withdraw
    #   (B - p + 1)*(S + O) >= (B + 1)*(S - s + O)
    lhs = (B - p + 1) * (S + O)
    rhs = (B + 1) * (S - s + O)
    if not (lhs >= rhs):
        v.append(("P1_withdraw_price_monotone",
                  dict(pre_S=S, pre_B=B, O=O, s=s, p=p, lhs=lhs, rhs=rhs)))
    # P1: structural solvency
    if not (p <= B):
        v.append(("P1_withdraw_solvency_p_le_B",
                  dict(pre_S=S, pre_B=B, O=O, s=s, p=p)))
    # P3(c): exact residue  s*(B+1) = p*(S+O) + r' , 0 <= r' < S + O
    r = s * (B + 1) - p * (S + O)
    if not (0 <= r < S + O):
        v.append(("P3c_withdraw_residue",
                  dict(pre_S=S, pre_B=B, O=O, s=s, p=p, r=r)))
    return v


def donate_property_violations(pre_S, pre_B, O, a):
    """P1: donating cannot decrease price (cross-multiplied)."""
    v = []
    # newprice (B+a+1)/(S+O) >= oldprice (B+1)/(S+O)
    lhs = (pre_B + a + 1) * (pre_S + O)
    rhs = (pre_B + 1) * (pre_S + O)
    if not (lhs >= rhs):
        v.append(("P1_donate_price_monotone",
                  dict(pre_S=pre_S, pre_B=pre_B, O=O, a=a)))
    return v


def anchor_violation(S, B, O):
    """P3(b) genesis anchor: O*B >= S (equivalently price >= 1/O)."""
    if not (O * B >= S):
        return [("P3b_anchor", dict(S=S, B=B, O=O))]
    return []


# ---------------------------------------------------------------------------
# Guard soundness (symbolic, no sweep).
# ---------------------------------------------------------------------------
def guard_margins(O=DEFAULT_O, MAXA=DEFAULT_MAXA, MAXS=DEFAULT_MAXS,
                  MAXB=DEFAULT_MAXB):
    """Return the two worst-case products and their bit-margins below 2^256."""
    bound = 2 ** 256
    prod_deposit = MAXA * (MAXS + O)      # deposit numerator worst case
    prod_withdraw = MAXS * (MAXB + 1)     # withdraw numerator worst case (s<=S<=MAXS)
    def bits(n):
        return n.bit_length()
    return {
        "bound_2^256_bits": 256,
        "deposit_MAXA*(MAXS+O)": prod_deposit,
        "deposit_bits": bits(prod_deposit),
        "deposit_margin_bits": 256 - bits(prod_deposit),
        "deposit_fits": prod_deposit < bound,
        "withdraw_MAXS*(MAXB+1)": prod_withdraw,
        "withdraw_bits": bits(prod_withdraw),
        "withdraw_margin_bits": 256 - bits(prod_withdraw),
        "withdraw_fits": prod_withdraw < bound,
    }


# ---------------------------------------------------------------------------
# Transcript execution (shared with harness + CLI).
# ---------------------------------------------------------------------------
def run_transcript(ops, O=DEFAULT_O, MAXA=DEFAULT_MAXA, MAXS=DEFAULT_MAXS,
                   MAXB=DEFAULT_MAXB, offset_enabled=True, verbose=False):
    """Execute a list of ops on a fresh model, returning the trace.

    Each op is a tuple: ("deposit", addr, a) | ("withdraw", addr, s) |
    ("donate", a). Reverts are recorded (state unchanged) rather than raised.
    """
    m = ProRata(O, MAXA, MAXS, MAXB, offset_enabled=offset_enabled)
    trace = []
    for i, op in enumerate(ops):
        pre = m.snapshot()
        kind = op[0]
        rec = {"step": i, "op": op, "pre_S": pre["S"], "pre_B": pre["B"]}
        try:
            if kind == "deposit":
                _, addr, a = op
                out = m.deposit(addr, a)
                rec.update(addr=addr, value=a, result=out, reverted=False)
            elif kind == "withdraw":
                _, addr, s = op
                out = m.withdraw(addr, s)
                rec.update(addr=addr, shares=s, result=out, reverted=False)
            elif kind == "donate":
                _, a = op
                m.donate(a)
                rec.update(value=a, result=None, reverted=False)
            else:
                raise ValueError(f"unknown op {op!r}")
        except Revert as e:
            rec.update(reverted=True, reason=e.reason, result=None)
        rec["post_S"] = m.S
        rec["post_B"] = m.B
        rec["post_ledger"] = dict(m.ledger)
        trace.append(rec)
        if verbose:
            print(json.dumps(rec, default=str))
    return m, trace


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def _cli(argv=None):
    p = argparse.ArgumentParser(description="PRORATA exact-arithmetic oracle")
    sub = p.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("guard-margins", help="print symbolic guard soundness")
    g.add_argument("--O", type=int, default=DEFAULT_O)
    g.add_argument("--MAXA", type=int, default=DEFAULT_MAXA)
    g.add_argument("--MAXS", type=int, default=DEFAULT_MAXS)
    g.add_argument("--MAXB", type=int, default=DEFAULT_MAXB)

    c = sub.add_parser("convert", help="evaluate the pure views at a state")
    c.add_argument("--O", type=int, default=DEFAULT_O)
    c.add_argument("--S", type=int, required=True)
    c.add_argument("--B", type=int, required=True)
    c.add_argument("--shares", type=int, help="convertToAssets(shares)")
    c.add_argument("--assets", type=int, help="convertToShares(assets)")

    t = sub.add_parser("transcript", help="run a JSON transcript from a file/stdin")
    t.add_argument("path", nargs="?", default="-",
                   help="JSON file of ops, or '-' for stdin")
    t.add_argument("--O", type=int, default=DEFAULT_O)
    t.add_argument("--disabled", action="store_true",
                   help="use the offset-disabled variant")

    d = sub.add_parser("demo", help="tiny self-check demo")

    args = p.parse_args(argv)

    if args.cmd == "guard-margins":
        gm = guard_margins(args.O, args.MAXA, args.MAXS, args.MAXB)
        for k, v in gm.items():
            print(f"{k}: {v}")
        return 0

    if args.cmd == "convert":
        model = ProRata(O=args.O)
        model.S = args.S
        model.B = args.B
        if args.assets is not None:
            try:
                print(f"convertToShares({args.assets}) = {model.convertToShares(args.assets)}")
            except Revert as e:
                print(f"convertToShares reverts: {e.reason}")
        if args.shares is not None:
            try:
                print(f"convertToAssets({args.shares}) = {model.convertToAssets(args.shares)}")
            except Revert as e:
                print(f"convertToAssets reverts: {e.reason}")
        return 0

    if args.cmd == "transcript":
        raw = sys.stdin.read() if args.path == "-" else open(args.path).read()
        ops = [tuple(o) for o in json.loads(raw)]
        _, trace = run_transcript(ops, O=args.O, offset_enabled=not args.disabled,
                                  verbose=True)
        return 0

    if args.cmd == "demo":
        model = ProRata()
        print("guard margins:", guard_margins())
        m1 = model.deposit("alice", 1_000_000)
        print("alice deposit 1e6 -> shares", m1, "state", model.S, model.B)
        model.donate(500_000)
        m2 = model.deposit("bob", 1_000_000)
        print("bob deposit 1e6 after donate -> shares", m2)
        p = model.withdraw("bob", m2)
        print("bob withdraw all -> assets", p, "loss", 1_000_000 - p)
        print("flags:", model.flags)
        return 0

    return 1


if __name__ == "__main__":
    raise SystemExit(_cli())
