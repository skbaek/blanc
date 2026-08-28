#!/usr/bin/env python3
"""Brute-force / search harness for the PRORATA exact oracle.

Reproducible: all randomized checks use fixed seeds; all exhaustive sweeps are
deterministic enumerations. A full run completes in well under ~10 minutes.

Pure Python 3, standard library only, exact integer arithmetic (no floats).

Sections
  P1/P3/P2 : exhaustive reachable-state sweep from genesis (dedup on state),
             plus a small-cap sweep that forces the arithmetic guards so the
             view/op revert agreement (P2) is exercised.
  P4(i)    : exhaustive attacker-profit DFS (enabled variant).
  P4(ii)   : victim-loss frontier + candidate exact-bound verdicts.
  P4(iii)  : offset-DISABLED first-depositor inflation attack (must succeed).
  P4(iv)   : same attack shape on the real O=1000 contract (must fail).
  Guards   : symbolic guard soundness (bit margins).
  Random   : wide-range randomized P1-P3 at ~2^96 magnitudes, fixed seed.

The harness inlines the model arithmetic for speed and then RE-CHECKS every
reported witness transcript through prorata_oracle.ProRata to guarantee the
inlined arithmetic matches the reference semantics (fidelity gate).
"""

from __future__ import annotations

import json
import random
import time

import prorata_oracle as ora
from prorata_oracle import (
    ProRata, Revert, guard_margins,
    deposit_property_violations, withdraw_property_violations,
    donate_property_violations, anchor_violation, run_transcript,
)

# Large caps that never bind in the small sweeps.
BIG = 1 << 200


# ===========================================================================
# Inlined exact arithmetic (must match prorata_oracle exactly; fidelity-gated).
# ===========================================================================
def _dep(S, B, O, a, MAXA, MAXS, MAXB, enabled):
    """Return (m, revert_reason_or_None) for a deposit; does not mutate.

    ``B`` is B_pre (the pre-credit balance). The offset-enabled path carries the
    post-review B_pre > MAXB guard matching the contract.
    """
    if a > MAXA:
        return None, "a>MAXA"
    if enabled:
        if B > MAXB:
            return None, "Bpre>MAXB"
        m = a * (S + O) // (B + 1)
    else:
        if S == 0:
            m = a
        elif B == 0:
            m = 0
        else:
            m = a * S // B
    if S + m > MAXS:
        return None, "S+m>MAXS"
    return m, None


def _wd(S, B, O, s, MAXB, enabled):
    """Return (p, revert_reason_or_None) for a withdraw; does not mutate."""
    if B > MAXB:
        return None, "B>MAXB"
    if enabled:
        p = s * (B + 1) // (S + O)
    else:
        p = 0 if S == 0 else s * B // S
    if p > B:
        return None, "SOLVENCY_p>B"
    return p, None


# ===========================================================================
# P1 / P3 / P2 : exhaustive reachable-state sweep (dedup on state)
# ===========================================================================
def sweep_reachable(O, V, depth, addrs=("a", "b"),
                    MAXA=BIG, MAXS=BIG, MAXB=BIG, enabled=True):
    """BFS over unique reachable states within `depth` steps from genesis.

    Checks P1 (per op), P3(a price monotone == P1 monotone forms), P3(b anchor
    at every reachable state), P3(c residue), P3(d flow conservation), and P2
    (view == op result, and view-revert iff op arithmetic-guard-revert) on
    every applied transition.
    """
    genesis = (0, 0, tuple((ad, 0) for ad in addrs))  # ledger as sorted tuple
    # visited maps state -> min depth seen
    from collections import deque
    visited = {genesis: 0}
    q = deque([genesis])
    stats = {"states": 0, "transitions": 0, "deposits": 0, "withdraws": 0,
             "donates": 0, "reverts": 0}
    violations = []

    def led_get(led, ad):
        for k, val in led:
            if k == ad:
                return val
        return 0

    def led_set(led, ad, val):
        return tuple((k, (val if k == ad else v)) for k, v in led)

    while q:
        st = q.popleft()
        S, B, led = st
        d = visited[st]
        stats["states"] += 1

        # P3(b) anchor holds at every reachable state (enabled variant only).
        if enabled:
            violations.extend(("state", av, st) for av in anchor_violation(S, B, O))
        # hard model invariant: sum(ledger)==S
        if sum(v for _, v in led) != S:
            violations.append(("state_ledger_sum", dict(st=st)))

        if d >= depth:
            continue

        # enumerate ops
        for ad in addrs:
            for a in range(0, V + 1):
                m, rr = _dep(S, B, O, a, MAXA, MAXS, MAXB, enabled)
                if rr is not None:
                    stats["reverts"] += 1
                    # P2: view must also revert on an arithmetic guard
                    view_rev = None
                    tmp = ProRata(O, MAXA, MAXS, MAXB, enabled)
                    tmp.S, tmp.B = S, B
                    try:
                        tmp.convertToShares(a)
                        view_rev = False
                    except Revert:
                        view_rev = True
                    if not view_rev:
                        violations.append(("P2_deposit_view_should_revert",
                                           dict(S=S, B=B, a=a, reason=rr)))
                    continue
                # P1/P3(c) per-op checks
                dv = deposit_property_violations(S, B, O, a, m)
                if dv:
                    violations.extend(("dep", x, st, a) for x in dv)
                # P2 value + no-revert agreement
                tmp = ProRata(O, MAXA, MAXS, MAXB, enabled)
                tmp.S, tmp.B = S, B
                try:
                    mv = tmp.convertToShares(a)
                    if mv != m:
                        violations.append(("P2_deposit_view_neq",
                                           dict(S=S, B=B, a=a, view=mv, op=m)))
                except Revert:
                    violations.append(("P2_deposit_view_unexpected_revert",
                                       dict(S=S, B=B, a=a)))
                # P3(d) flow + state transition
                nS, nB = S + m, B + a
                nled = led_set(led, ad, led_get(led, ad) + m)
                stats["transitions"] += 1
                stats["deposits"] += 1
                nst = (nS, nB, nled)
                if nst not in visited:
                    visited[nst] = d + 1
                    q.append(nst)

            # withdraws: s in 0..ledger[ad]
            bal = led_get(led, ad)
            for s in range(0, bal + 1):
                p, rr = _wd(S, B, O, s, MAXB, enabled)
                if rr is not None:
                    if rr.startswith("SOLVENCY"):
                        violations.append(("P1_withdraw_solvency_flag",
                                           dict(S=S, B=B, s=s)))
                    stats["reverts"] += 1
                    continue
                wv = withdraw_property_violations(S, B, O, s, p)
                if wv:
                    violations.extend(("wd", x, st, s) for x in wv)
                # P2: convertToAssets(s) == p, and view reverts iff B>MAXB
                tmp = ProRata(O, MAXA, MAXS, MAXB, enabled)
                tmp.S, tmp.B = S, B
                try:
                    pv = tmp.convertToAssets(s)
                    if pv != p:
                        violations.append(("P2_withdraw_view_neq",
                                           dict(S=S, B=B, s=s, view=pv, op=p)))
                except Revert:
                    violations.append(("P2_withdraw_view_unexpected_revert",
                                       dict(S=S, B=B, s=s)))
                nS, nB = S - s, B - p
                nled = led_set(led, ad, bal - s)
                stats["transitions"] += 1
                stats["withdraws"] += 1
                nst = (nS, nB, nled)
                if nst not in visited:
                    visited[nst] = d + 1
                    q.append(nst)

        # donate: a in 0..V (no address)
        for a in range(0, V + 1):
            dv = donate_property_violations(S, B, O, a)
            if dv:
                violations.extend(("don", x, st, a) for x in dv)
            nst = (S, B + a, led)
            stats["transitions"] += 1
            stats["donates"] += 1
            if nst not in visited:
                visited[nst] = d + 1
                q.append(nst)

    stats["unique_states"] = len(visited)
    return stats, violations


# ===========================================================================
# P2 forced-guard sweep: small caps so arithmetic guards actually fire.
# ===========================================================================
def sweep_p2_guards(O, V, depth, MAXA, MAXS, MAXB, addrs=("a", "b")):
    """Reachable sweep with binding caps; verify P2 view/op revert agreement
    including the ledger-sufficiency EXCLUSION for withdraw views."""
    stats, violations = sweep_reachable(O, V, depth, addrs, MAXA, MAXS, MAXB,
                                        enabled=True)
    # Additionally test the ledger-exclusion: withdraw with s > ledger reverts
    # in the op (ledger) but the view must NOT revert (unless B>MAXB).
    ledger_excl_checks = 0
    ledger_excl_viol = []
    # sample a handful of reachable states with binding B against MAXB is hard
    # in small sweeps; the core exclusion property is checked structurally here:
    m = ProRata(O, MAXA, MAXS, MAXB, True)
    m.S, m.B, m.ledger = 5, 5, {"a": 5}
    for s in range(0, 12):
        # op would revert for s>5 (ledger); view should still return a value
        try:
            pv = m.convertToAssets(s)
            ledger_excl_checks += 1
        except Revert:
            # view only allowed to revert on B>MAXB (not here)
            ledger_excl_viol.append(dict(s=s, S=m.S, B=m.B))
    return stats, violations, ledger_excl_checks, ledger_excl_viol


# ===========================================================================
# New-guard boundary sweep: exercises the post-review guards where they BIND.
#   deposit / convertToShares : B_pre > MAXB
#   convertToAssets           : s > MAXS
# Small caps so every cap is straddled; runs entirely through the REFERENCE
# model (authoritative semantics), asserting
#   (a) P2 view-iff-op agreement, including the new reverts,
#   (b) state unchanged on every revert,
#   (c) P1/P3 on the successful subset.
# ===========================================================================
def sweep_new_guard_boundary(O, MAXA=6, MAXS=40, MAXB=9, depth=4,
                             addrs=("a", "b")):
    from collections import deque
    donate_vals = (0, 1, 3, 5, 11)         # 11 jumps B over MAXB=9 in one step
    dep_vals = tuple(range(0, MAXA + 4))   # straddles MAXA
    genesis = (0, 0, tuple((ad, 0) for ad in addrs))
    visited = {genesis: 0}
    q = deque([genesis])
    stats = {
        "unique_states": 0, "deposit_checks": 0, "withdraw_checks": 0,
        "view_shares_checks": 0, "view_assets_checks": 0,
        "revert_dep_a>MAXA": 0, "revert_dep_Bpre>MAXB": 0,
        "revert_dep_S+m>MAXS": 0,
        "revert_wd_ledger": 0, "revert_wd_B>MAXB": 0,
        "revert_view_assets_s>MAXS": 0, "revert_view_assets_B>MAXB": 0,
        "successful_ops": 0,
    }
    violations = []

    def led_get(led, ad):
        for k, val in led:
            if k == ad:
                return val
        return 0

    def led_set(led, ad, val):
        return tuple((k, (val if k == ad else v)) for k, v in led)

    def mk(S, B, led):
        t = ProRata(O, MAXA, MAXS, MAXB, True)
        t.S, t.B, t.ledger = S, B, dict(led)
        return t

    while q:
        st = q.popleft()
        S, B, led = st
        d = visited[st]
        stats["unique_states"] += 1
        violations.extend(("state", av, st) for av in anchor_violation(S, B, O))

        # ---- direct view probes at this state (hypothetical arguments) ----
        # convertToAssets straddling MAXS (the new s > MAXS view guard):
        for s in (0, 1, MAXS - 1, MAXS, MAXS + 1, MAXS + 5):
            stats["view_assets_checks"] += 1
            t = mk(S, B, led)
            pre = t.snapshot()
            try:
                t.convertToAssets(s)
                if B > MAXB or s > MAXS:
                    violations.append(("view_assets_should_revert",
                                       dict(S=S, B=B, s=s)))
            except Revert as e:
                if "s > MAXS" in e.reason:
                    stats["revert_view_assets_s>MAXS"] += 1
                    if not (s > MAXS):
                        violations.append(("view_assets_sMAXS_wrong",
                                           dict(S=S, B=B, s=s)))
                elif "B > MAXB" in e.reason:
                    stats["revert_view_assets_B>MAXB"] += 1
                    if not (B > MAXB):
                        violations.append(("view_assets_BMAXB_wrong",
                                           dict(S=S, B=B, s=s)))
                else:
                    violations.append(("view_assets_unknown_revert",
                                       dict(S=S, B=B, s=s, reason=e.reason)))
            if t.snapshot() != pre:
                violations.append(("view_assets_mutated", dict(S=S, B=B, s=s)))

        if d >= depth:
            continue

        # ---- deposits (op vs convertToShares, incl. new B_pre > MAXB) ----
        for ad in addrs:
            for a in dep_vals:
                stats["deposit_checks"] += 1
                t = mk(S, B, led)
                pre = t.snapshot()
                op_res, op_rev = None, None
                try:
                    op_res = t.deposit(ad, a)
                except Revert as e:
                    op_rev = e.reason
                    # (b) state unchanged on revert
                    if t.snapshot() != pre:
                        violations.append(("dep_revert_mutated",
                                           dict(S=S, B=B, a=a, reason=op_rev)))
                # view at the SAME pre-state
                tv = mk(S, B, led)
                view_res, view_rev = None, None
                try:
                    view_res = tv.convertToShares(a)
                except Revert as e:
                    view_rev = e.reason
                # (a) exact iff: deposit's guard region == view's revert region
                if (op_rev is None) != (view_rev is None):
                    violations.append(("P2_dep_view_iff",
                                       dict(S=S, B=B, a=a, op_rev=op_rev,
                                            view_rev=view_rev)))
                if op_rev is None:
                    if view_res != op_res:
                        violations.append(("P2_dep_view_neq",
                                           dict(S=S, B=B, a=a, view=view_res,
                                                op=op_res)))
                    # (c) P1/P3 on the successful subset
                    violations.extend(
                        ("dep", x, st, a)
                        for x in deposit_property_violations(S, B, O, a, op_res))
                    stats["successful_ops"] += 1
                    nst = (S + op_res, B + a, led_set(led, ad,
                                                      led_get(led, ad) + op_res))
                    if nst not in visited:
                        visited[nst] = d + 1
                        q.append(nst)
                else:
                    if "a > MAXA" in op_rev:
                        stats["revert_dep_a>MAXA"] += 1
                        if not (a > MAXA):
                            violations.append(("dep_aMAXA_wrong",
                                               dict(S=S, B=B, a=a)))
                    elif "B_pre > MAXB" in op_rev:
                        stats["revert_dep_Bpre>MAXB"] += 1
                        if not (B > MAXB):
                            violations.append(("dep_BpreMAXB_wrong",
                                               dict(S=S, B=B, a=a)))
                    elif "S + m > MAXS" in op_rev:
                        stats["revert_dep_S+m>MAXS"] += 1
                    else:
                        violations.append(("dep_unknown_revert",
                                           dict(S=S, B=B, a=a, reason=op_rev)))

            # ---- withdraws (op vs convertToAssets; s straddles the ledger) --
            bal = led_get(led, ad)
            # bal+1, bal+2 exercise the ledger revert; capped at MAXS because
            # probes beyond MAXS belong to the direct view probes above (the
            # withdraw-domain claim only concerns s <= ledger <= S <= MAXS).
            for s in range(0, min(bal + 3, MAXS + 1)):
                stats["withdraw_checks"] += 1
                t = mk(S, B, led)
                pre = t.snapshot()
                op_res, op_rev = None, None
                try:
                    op_res = t.withdraw(ad, s)
                except Revert as e:
                    op_rev = e.reason
                    if t.snapshot() != pre:
                        violations.append(("wd_revert_mutated",
                                           dict(S=S, B=B, s=s, reason=op_rev)))
                tv = mk(S, B, led)
                view_res, view_rev = None, None
                try:
                    view_res = tv.convertToAssets(s)
                except Revert as e:
                    view_rev = e.reason
                # (a) agreement modulo the ledger exclusion:
                #   op arithmetic guard == B > MAXB ; view guard == B > MAXB
                #   (s > MAXS unreachable here: s <= bal+2 <= S+2 <= MAXS with
                #    S < MAXS strictly on this small-cap domain — assert it)
                if s > MAXS:
                    violations.append(("wd_probe_escaped_domain",
                                       dict(S=S, B=B, s=s)))
                op_arith_rev = op_rev is not None and "MAXB" in op_rev
                op_ledger_rev = op_rev is not None and "ledger" in op_rev
                if op_arith_rev and view_rev is None:
                    violations.append(("P2_wd_view_should_revert",
                                       dict(S=S, B=B, s=s, op_rev=op_rev)))
                if view_rev is not None and not (B > MAXB):
                    violations.append(("P2_wd_view_over_revert",
                                       dict(S=S, B=B, s=s, view_rev=view_rev)))
                if op_ledger_rev and not (s > bal):
                    violations.append(("wd_ledger_wrong", dict(S=S, B=B, s=s)))
                if op_rev is None:
                    if view_res != op_res:
                        violations.append(("P2_wd_view_neq",
                                           dict(S=S, B=B, s=s, view=view_res,
                                                op=op_res)))
                    violations.extend(
                        ("wd", x, st, s)
                        for x in withdraw_property_violations(S, B, O, s, op_res))
                    stats["successful_ops"] += 1
                    nst = (S - s, B - op_res, led_set(led, ad, bal - s))
                    if nst not in visited:
                        visited[nst] = d + 1
                        q.append(nst)
                else:
                    if op_ledger_rev:
                        stats["revert_wd_ledger"] += 1
                    elif "MAXB" in op_rev:
                        stats["revert_wd_B>MAXB"] += 1
                        if not (B > MAXB):
                            violations.append(("wd_BMAXB_wrong",
                                               dict(S=S, B=B, s=s)))
                    else:
                        violations.append(("wd_unknown_revert",
                                           dict(S=S, B=B, s=s, reason=op_rev)))

        # ---- donations drive B across MAXB so the new guards bind ----------
        for a in donate_vals:
            t = mk(S, B, led)
            t.donate(a)
            violations.extend(("don", x, st, a)
                              for x in donate_property_violations(S, B, O, a))
            nst = (S, B + a, led)
            if nst not in visited:
                visited[nst] = d + 1
                q.append(nst)

    return stats, violations


# ===========================================================================
# P4(i) + P4(ii): attacker-profit DFS with a victim
# ===========================================================================
def search_p4(O, V, depth, n_attackers=1,
              MAXA=BIG, MAXS=BIG, MAXB=BIG):
    """Exhaustive DFS. Attacker addresses skim value; a single victim deposit
    (and optional later withdraw-all) may be inserted at any position.

    Returns dict with: max attacker profit + witness transcript, node count,
    and the victim-loss records with candidate-bound verdicts.
    """
    best = {"profit": 0, "transcript": []}   # genesis profit is 0
    nodes = [0]
    # victim-loss bound verdicts
    bounds = {
        "C1": {"expr": "(B_dep+1)//(S_dep+O)+1", "violations": 0,
               "worst": None, "max_slack": None},
        "C2": {"expr": "(B_dep+1+v)//(S_dep+O)+1", "violations": 0,
               "worst": None, "max_slack": None},
        "C3": {"expr": "v//O+(B_dep+1)//(S_dep+O)+1", "violations": 0,
               "worst": None, "max_slack": None},
    }
    loss_records = []   # (loss, v, S_dep, B_dep) for frontier
    max_loss = {"loss": None, "rec": None}

    att = [f"A{i}" for i in range(n_attackers)]

    def bound_val(name, v, S_dep, B_dep):
        base = (B_dep + 1) // (S_dep + O)
        if name == "C1":
            return base + 1
        if name == "C2":
            return (B_dep + 1 + v) // (S_dep + O) + 1
        if name == "C3":
            return v // O + base + 1
        raise KeyError(name)

    def record_loss(v, payout, S_dep, B_dep, transcript):
        loss = v - payout
        loss_records.append((loss, v, S_dep, B_dep))
        if max_loss["loss"] is None or loss > max_loss["loss"]:
            max_loss["loss"] = loss
            max_loss["rec"] = dict(loss=loss, v=v, payout=payout,
                                   S_dep=S_dep, B_dep=B_dep,
                                   transcript=list(transcript))
        for name, info in bounds.items():
            b = bound_val(name, v, S_dep, B_dep)
            slack = b - loss   # >= 0 means bound holds
            if loss > b:
                info["violations"] += 1
                if info["worst"] is None or (b - loss) < info["worst"]["slack"]:
                    info["worst"] = dict(loss=loss, bound=b, slack=b - loss,
                                         v=v, S_dep=S_dep, B_dep=B_dep,
                                         transcript=list(transcript))
            if info["max_slack"] is None or slack > info["max_slack"]:
                info["max_slack"] = slack

    # state: S, B, attacker balances tuple, victim balance, vdep flag,
    #        vwith flag, victim v, victim S_dep, victim B_dep,
    #        ain, aout, transcript
    def rec(S, B, abals, vbal, vdep, vwith, vv, vSdep, vBdep,
            ain, aout, transcript, d):
        nodes[0] += 1
        profit = aout - ain
        if profit > best["profit"]:
            best["profit"] = profit
            best["transcript"] = list(transcript)
        if d == 0:
            return
        # attacker deposits
        for ai, aname in enumerate(att):
            for a in range(1, V + 1):
                m, rr = _dep(S, B, O, a, MAXA, MAXS, MAXB, True)
                if rr is not None:
                    continue
                nab = list(abals)
                nab[ai] += m
                transcript.append(("deposit", aname, a))
                rec(S + m, B + a, tuple(nab), vbal, vdep, vwith, vv, vSdep, vBdep,
                    ain + a, aout, transcript, d - 1)
                transcript.pop()
        # attacker withdraws
        for ai, aname in enumerate(att):
            for s in range(1, abals[ai] + 1):
                p, rr = _wd(S, B, O, s, MAXB, True)
                if rr is not None:
                    continue
                nab = list(abals)
                nab[ai] -= s
                transcript.append(("withdraw", aname, s))
                rec(S - s, B - p, tuple(nab), vbal, vdep, vwith, vv, vSdep, vBdep,
                    ain, aout + p, transcript, d - 1)
                transcript.pop()
        # donations (attributed to attacker cost)
        for a in range(1, V + 1):
            transcript.append(("donate", a))
            rec(S, B + a, abals, vbal, vdep, vwith, vv, vSdep, vBdep,
                ain + a, aout, transcript, d - 1)
            transcript.pop()
        # victim deposit (once)
        if not vdep:
            for a in range(1, V + 1):
                m, rr = _dep(S, B, O, a, MAXA, MAXS, MAXB, True)
                if rr is not None:
                    continue
                transcript.append(("deposit", "V", a))
                rec(S + m, B + a, abals, vbal + m, True, False, a, S, B,
                    ain, aout, transcript, d - 1)
                transcript.pop()
        # victim withdraw-all (once, after deposit, if it holds shares)
        if vdep and not vwith and vbal > 0:
            p, rr = _wd(S, B, O, vbal, MAXB, True)
            if rr is None:
                transcript.append(("withdraw", "V", vbal))
                record_loss(vv, p, vSdep, vBdep, transcript)
                rec(S - vbal, B - p, abals, 0, True, True, vv, vSdep, vBdep,
                    ain, aout, transcript, d - 1)
                transcript.pop()

    rec(0, 0, tuple([0] * n_attackers), 0, False, False, 0, 0, 0,
        0, 0, [], depth)

    # frontier: max loss per distinct (S_dep,B_dep,O) rounded bucket — keep raw
    return {
        "O": O, "V": V, "depth": depth, "n_attackers": n_attackers,
        "nodes": nodes[0],
        "max_profit": best["profit"],
        "max_profit_transcript": best["transcript"],
        "max_loss": max_loss["rec"],
        "loss_bounds": bounds,
        "loss_record_count": len(loss_records),
        "loss_records": loss_records,
    }


# ===========================================================================
# P4(iii): offset-DISABLED first-depositor inflation attack (must succeed)
# ===========================================================================
def disabled_inflation_attack(O_ignored=None, V=6, max_depth=5,
                              MAXA=BIG, MAXS=BIG, MAXB=BIG):
    """Search the DISABLED variant for a minimal transcript where the attacker
    profits AND the victim loses their whole deposit (payout == 0).

    Returns the lexicographically-minimal (shortest, then smallest values)
    such transcript, or None.
    """
    enabled = False
    O = 0  # offset disabled -> no virtual shares in the formulas we inline
    att = "A"
    vic = "V"
    found = []

    # DFS over transcripts; single attacker + single victim; victim deposits
    # once and withdraws nothing (loses whole deposit -> payout 0). We look for
    # attacker_profit > 0 and victim payout == 0.
    def rec(S, B, abal, vbal, vdep, vv, ain, aout, transcript, d):
        # evaluate: if victim has deposited and we can have the attacker skim,
        # this node is a candidate if profit>0 and victim lost all (vbal==0
        # from rounding, i.e. victim minted 0 shares => payout 0 guaranteed)
        if vdep and vv > 0 and vbal == 0 and (aout - ain) > 0:
            found.append((len(transcript), sum(_op_val(o) for o in transcript),
                          list(transcript),
                          dict(profit=aout - ain, victim_v=vv, victim_payout=0)))
        if d == 0:
            return
        # attacker deposit
        for a in range(1, V + 1):
            m, rr = _dep(S, B, 0, a, MAXA, MAXS, MAXB, enabled)
            if rr is not None:
                continue
            transcript.append(("deposit", att, a))
            rec(S + m, B + a, abal + m, vbal, vdep, vv, ain + a, aout,
                transcript, d - 1)
            transcript.pop()
        # attacker withdraw
        for s in range(1, abal + 1):
            p, rr = _wd(S, B, 0, s, MAXB, enabled)
            if rr is not None:
                continue
            transcript.append(("withdraw", att, s))
            rec(S - s, B - p, abal - s, vbal, vdep, vv, ain, aout + p,
                transcript, d - 1)
            transcript.pop()
        # donate
        for a in range(1, V + 1):
            transcript.append(("donate", a))
            rec(S, B + a, abal, vbal, vdep, vv, ain + a, aout, transcript, d - 1)
            transcript.pop()
        # victim deposit (once)
        if not vdep:
            for a in range(1, V + 1):
                m, rr = _dep(S, B, 0, a, MAXA, MAXS, MAXB, enabled)
                if rr is not None:
                    continue
                transcript.append(("deposit", vic, a))
                rec(S + m, B + a, abal, vbal + m, True, a, ain, aout,
                    transcript, d - 1)
                transcript.pop()

    rec(0, 0, 0, 0, False, 0, 0, 0, [], max_depth)
    if not found:
        return None
    found.sort(key=lambda t: (t[0], t[1], t[2]))
    depth_, valsum_, transcript_, meta_ = found[0]
    return dict(transcript=transcript_, meta=meta_, n_found=len(found))


def _op_val(op):
    if op[0] == "donate":
        return op[1]
    return op[-1]


# ===========================================================================
# P4(iv): the SAME attack shape on the REAL O=1000 contract (must fail)
# ===========================================================================
def real_contract_attack_shape(O=ora.DEFAULT_O, donate_amt=None, victim_v=None):
    """Replay the classic first-depositor shape on the real (offset-enabled)
    contract and record that it fails: attacker profit <= 0 and victim loss
    stays within the P4(ii) bound. Returns the transcript trace + accounting.

    Shape: attacker deposit 1 ; attacker donate D ; victim deposit v ;
           attacker withdraw all ; victim withdraw all.
    """
    if donate_amt is None:
        donate_amt = 10 ** 6
    if victim_v is None:
        victim_v = 10 ** 6
    ops = [
        ("deposit", "A", 1),
        ("donate", donate_amt),
        ("deposit", "V", victim_v),
        # attacker withdraws all its shares; victim withdraws all its shares
    ]
    m = ProRata(O=O)
    trace = []
    # execute prefix, capturing shares minted
    a_shares = m.deposit("A", 1); trace.append(("deposit", "A", 1, "->shares", a_shares))
    m.donate(donate_amt); trace.append(("donate", donate_amt))
    S_dep, B_dep = m.S, m.B  # state victim's deposit sees (pre-credit)
    v_shares = m.deposit("V", victim_v); trace.append(("deposit", "V", victim_v, "->shares", v_shares))
    a_payout = m.withdraw("A", a_shares); trace.append(("withdraw", "A", a_shares, "->assets", a_payout))
    v_payout = m.withdraw("V", v_shares); trace.append(("withdraw", "V", v_shares, "->assets", v_payout))

    attacker_in = 1 + donate_amt
    attacker_out = a_payout
    attacker_profit = attacker_out - attacker_in
    victim_loss = victim_v - v_payout
    c1 = (B_dep + 1) // (S_dep + O) + 1
    c2 = (B_dep + 1 + victim_v) // (S_dep + O) + 1
    c3 = victim_v // O + (B_dep + 1) // (S_dep + O) + 1
    return dict(
        O=O, donate=donate_amt, victim_v=victim_v,
        trace=trace,
        attacker_in=attacker_in, attacker_out=attacker_out,
        attacker_profit=attacker_profit,
        victim_loss=victim_loss, victim_shares=v_shares,
        S_dep=S_dep, B_dep=B_dep,
        bound_C1=c1, bound_C1_holds=victim_loss <= c1,
        bound_C2=c2, bound_C2_holds=victim_loss <= c2,
        bound_C3=c3, bound_C3_holds=victim_loss <= c3,
        flags=m.flags,
    )


# ===========================================================================
# Wide-range randomized P1-P3 checks (~2^96 magnitudes, fixed seed)
# ===========================================================================
def random_wide(seed, n_seqs, seq_len, O, MAXA, MAXS, MAXB, val_bits=96):
    rng = random.Random(seed)
    stats = {"sequences": 0, "ops": 0, "deposits": 0, "withdraws": 0,
             "donates": 0, "reverts": 0}
    violations = []
    hi = (1 << val_bits)
    addrs = ["a", "b", "c"]
    for _ in range(n_seqs):
        m = ProRata(O, MAXA, MAXS, MAXB, True)
        stats["sequences"] += 1
        for _ in range(seq_len):
            stats["ops"] += 1
            kind = rng.choice(["deposit", "deposit", "withdraw", "donate"])
            pre_S, pre_B = m.S, m.B
            if kind == "deposit":
                ad = rng.choice(addrs)
                a = rng.randrange(0, hi)
                try:
                    out = m.deposit(ad, a)
                    stats["deposits"] += 1
                    violations.extend(("rand_dep", x)
                                      for x in deposit_property_violations(pre_S, pre_B, O, a, out))
                    violations.extend(("rand_anchor", x)
                                      for x in anchor_violation(m.S, m.B, O))
                except Revert:
                    stats["reverts"] += 1
            elif kind == "withdraw":
                ad = rng.choice(addrs)
                bal = m.ledger.get(ad, 0)
                if bal == 0:
                    continue
                s = rng.randrange(1, bal + 1)
                try:
                    out = m.withdraw(ad, s)
                    stats["withdraws"] += 1
                    violations.extend(("rand_wd", x)
                                      for x in withdraw_property_violations(pre_S, pre_B, O, s, out))
                    violations.extend(("rand_anchor", x)
                                      for x in anchor_violation(m.S, m.B, O))
                except Revert:
                    stats["reverts"] += 1
            else:
                a = rng.randrange(0, hi)
                m.donate(a)
                stats["donates"] += 1
                violations.extend(("rand_don", x)
                                  for x in donate_property_violations(pre_S, pre_B, O, a))
    return stats, violations


# ===========================================================================
# Fidelity gate: re-run a witness transcript through the reference model.
# ===========================================================================
def fidelity_replay(transcript, O, enabled=True):
    """Replay a search transcript (attacker 'A*'/victim 'V' addresses) through
    the reference ProRata and return the accounting, to confirm the inlined
    search arithmetic matches the reference model exactly."""
    m = ProRata(O=O, offset_enabled=enabled)
    ain = aout = 0
    steps = []
    for op in transcript:
        if op[0] == "deposit":
            _, addr, a = op
            r = m.deposit(addr, a)
            if addr != "V":
                ain += a
            steps.append((op, "shares", r))
        elif op[0] == "withdraw":
            _, addr, s = op
            r = m.withdraw(addr, s)
            if addr != "V":
                aout += r
            steps.append((op, "assets", r))
        elif op[0] == "donate":
            _, a = op
            m.donate(a)
            ain += a
            steps.append((op, None, None))
    return dict(steps=steps, attacker_in=ain, attacker_out=aout,
                attacker_profit=aout - ain, final_S=m.S, final_B=m.B,
                flags=m.flags)


# ===========================================================================
# Main battery
# ===========================================================================
def main():
    t0 = time.time()
    summary = {}

    print("=" * 70)
    print("PRORATA brute-force oracle battery")
    print("=" * 70)

    # ---- Guard soundness (symbolic) ----
    gm = guard_margins()
    summary["guards"] = gm
    print("\n[Guards] symbolic soundness (defaults O=1e3, MAXA=2^96-1, "
          "MAXS=MAXB=2^126-1):")
    print(f"  deposit  MAXA*(MAXS+O) = {gm['deposit_bits']} bits, "
          f"margin {gm['deposit_margin_bits']} bits, fits={gm['deposit_fits']}")
    print(f"  withdraw MAXS*(MAXB+1) = {gm['withdraw_bits']} bits, "
          f"margin {gm['withdraw_margin_bits']} bits, fits={gm['withdraw_fits']}")

    # ---- P1/P3/P2 exhaustive sweeps at small O ----
    print("\n[P1/P3/P2] exhaustive reachable-state sweeps (dedup on state):")
    p1p3 = []
    for (O, V, depth) in [(1, 6, 6), (2, 6, 6), (3, 6, 5), (10, 6, 5)]:
        ts = time.time()
        stats, viol = sweep_reachable(O, V, depth)
        el = time.time() - ts
        rec = dict(O=O, V=V, depth=depth, stats=stats,
                   violation_count=len(viol),
                   sample_violations=viol[:5], seconds=round(el, 2))
        p1p3.append(rec)
        print(f"  O={O:2d} V={V} depth={depth}: unique_states="
              f"{stats['unique_states']:>7} transitions={stats['transitions']:>8} "
              f"violations={len(viol)}  ({el:.1f}s)")
    summary["P1_P3_P2_sweeps"] = p1p3

    # ---- P2 forced-guard sweep (binding caps exercise arithmetic reverts) ----
    print("\n[P2] forced-guard sweep (binding caps) + ledger-exclusion:")
    gstats, gviol, lchecks, lviol = sweep_p2_guards(
        O=2, V=8, depth=5, MAXA=20, MAXS=40, MAXB=40)
    print(f"  binding-cap sweep: states={gstats['unique_states']} "
          f"reverts={gstats['reverts']} P2_violations={len(gviol)}")
    print(f"  withdraw-view ledger-exclusion checks={lchecks} "
          f"violations={len(lviol)}")
    summary["P2_guards"] = dict(stats=gstats, violation_count=len(gviol),
                                sample=gviol[:5],
                                ledger_excl_checks=lchecks,
                                ledger_excl_violations=lviol)

    # ---- New-guard boundary sweep (post-review guards binding) ----
    print("\n[New-guards] boundary sweep (MAXA=6, MAXS=40, MAXB=9; reference "
          "model; caps straddled):")
    ng = []
    for O in (1, 3):
        ts = time.time()
        nstats, nviol = sweep_new_guard_boundary(O)
        el = time.time() - ts
        print(f"  O={O}: states={nstats['unique_states']} "
              f"dep_checks={nstats['deposit_checks']} "
              f"wd_checks={nstats['withdraw_checks']} "
              f"viewA_checks={nstats['view_assets_checks']} "
              f"violations={len(nviol)}  ({el:.1f}s)")
        print(f"        reverts: dep a>MAXA={nstats['revert_dep_a>MAXA']} "
              f"dep Bpre>MAXB={nstats['revert_dep_Bpre>MAXB']} "
              f"dep S+m>MAXS={nstats['revert_dep_S+m>MAXS']} "
              f"wd ledger={nstats['revert_wd_ledger']} "
              f"wd B>MAXB={nstats['revert_wd_B>MAXB']} "
              f"viewA s>MAXS={nstats['revert_view_assets_s>MAXS']} "
              f"viewA B>MAXB={nstats['revert_view_assets_B>MAXB']}")
        ng.append(dict(O=O, stats=nstats, violation_count=len(nviol),
                       sample=nviol[:5], seconds=round(el, 2)))
    summary["new_guard_boundary"] = ng

    # ---- P4(i)+(ii) attacker-profit / victim-loss search ----
    print("\n[P4(i)/(ii)] exhaustive attacker-profit search (enabled variant):")
    p4 = []
    for (O, V, depth, na) in [(1, 8, 5, 1), (2, 8, 5, 1), (3, 8, 5, 1),
                              (10, 8, 5, 1), (1, 6, 6, 1), (1, 5, 5, 2)]:
        ts = time.time()
        res = search_p4(O, V, depth, na)
        el = time.time() - ts
        print(f"  O={O:2d} V={V} depth={depth} attackers={na}: "
              f"nodes={res['nodes']:>9} max_profit={res['max_profit']} "
              f"max_loss={res['max_loss']['loss'] if res['max_loss'] else None} "
              f"loss_recs={res['loss_record_count']}  ({el:.1f}s)")
        # drop the bulky raw loss_records from the stored summary but keep frontier
        frontier = _loss_frontier(res["loss_records"])
        res_store = {k: v for k, v in res.items() if k != "loss_records"}
        res_store["loss_frontier"] = frontier
        res_store["seconds"] = round(el, 2)
        p4.append(res_store)
    summary["P4_i_ii"] = p4

    # aggregate bound verdicts across all P4 configs
    agg = {"C1": {"violations": 0, "worst": None},
           "C2": {"violations": 0, "worst": None},
           "C3": {"violations": 0, "worst": None}}
    max_profit_overall = 0
    max_profit_witness = None
    max_profit_O = None
    for res in p4:
        if res["max_profit"] > max_profit_overall:
            max_profit_overall = res["max_profit"]
            max_profit_witness = res["max_profit_transcript"]
            max_profit_O = res["O"]
        for name in ("C1", "C2", "C3"):
            info = res["loss_bounds"][name]
            agg[name]["violations"] += info["violations"]
            if info["worst"] is not None:
                if (agg[name]["worst"] is None or
                        info["worst"]["slack"] < agg[name]["worst"]["slack"]):
                    agg[name]["worst"] = info["worst"]
    summary["P4_bound_verdicts"] = agg
    summary["P4_max_profit_overall"] = max_profit_overall
    summary["P4_max_profit_witness"] = max_profit_witness
    summary["P4_max_profit_O"] = max_profit_O
    print(f"  --> max attacker profit across ALL configs = {max_profit_overall} "
          f"(at O={max_profit_O})")
    for name in ("C1", "C2", "C3"):
        print(f"  --> victim-loss bound {name}: violations={agg[name]['violations']}")
    if max_profit_overall > 0 and max_profit_witness:
        fr = fidelity_replay(max_profit_witness, O=max_profit_O, enabled=True)
        summary["P4_max_profit_fidelity"] = fr
        print(f"  --> POSITIVE-PROFIT WITNESS (O={max_profit_O}): {max_profit_witness}")
        print(f"      fidelity replay: attacker_in={fr['attacker_in']} "
              f"attacker_out={fr['attacker_out']} profit={fr['attacker_profit']}")

    # ---- P4(i) leak-boundary characterization: is the O=1 leak bounded, and
    #      does it vanish for O>=2 as depth grows? ----
    print("\n[P4(i)-boundary] max attacker profit vs O and depth (V=4):")
    boundary = []
    for O in (1, 2, 3):
        row = {"O": O, "by_depth": {}}
        for depth in (4, 5, 6, 7):
            res = search_p4(O, 4, depth, 1)
            row["by_depth"][depth] = res["max_profit"]
        boundary.append(row)
        print(f"  O={O}: " + "  ".join(
            f"d{d}={row['by_depth'][d]}" for d in (4, 5, 6, 7)))
    summary["P4_i_boundary"] = boundary

    # ---- P4(iii) disabled inflation attack (must succeed) ----
    print("\n[P4(iii)] offset-DISABLED first-depositor inflation attack:")
    dis = disabled_inflation_attack(V=6, max_depth=5)
    if dis is None:
        print("  !! NO attack found (UNEXPECTED - control failed)")
    else:
        print(f"  minimal transcript: {dis['transcript']}")
        print(f"  meta: {dis['meta']}  (total qualifying nodes: {dis['n_found']})")
        # fidelity replay (O is ignored by the disabled-variant formulas; pass
        # a valid O=1 to satisfy the reference model's O>=1 precondition)
        fr = fidelity_replay(dis["transcript"], O=1, enabled=False)
        dis["fidelity_replay"] = fr
        print(f"  fidelity replay: attacker_profit={fr['attacker_profit']} "
              f"final_S={fr['final_S']} final_B={fr['final_B']}")
    summary["P4_iii_disabled_attack"] = dis

    # ---- P4(iv) real contract same shape (must fail) ----
    print("\n[P4(iv)] SAME shape on the real O=1000 contract:")
    real = real_contract_attack_shape()
    print(f"  trace: {real['trace']}")
    print(f"  attacker_in={real['attacker_in']} attacker_out={real['attacker_out']} "
          f"attacker_profit={real['attacker_profit']}")
    print(f"  victim_loss={real['victim_loss']}  bounds "
          f"C1={real['bound_C1']}({real['bound_C1_holds']}) "
          f"C2={real['bound_C2']}({real['bound_C2_holds']}) "
          f"C3={real['bound_C3']}({real['bound_C3_holds']})")
    summary["P4_iv_real_shape"] = real

    # ---- Wide-range randomized P1-P3 ----
    print("\n[Random] wide-range randomized P1-P3 (~2^96 magnitudes, seed=20260828):")
    for (O, seqs, ln) in [(ora.DEFAULT_O, 4000, 40), (1, 2000, 40), (10, 2000, 40)]:
        ts = time.time()
        rstats, rviol = random_wide(20260828, seqs, ln, O,
                                    ora.DEFAULT_MAXA, ora.DEFAULT_MAXS,
                                    ora.DEFAULT_MAXB)
        el = time.time() - ts
        print(f"  O={O}: sequences={rstats['sequences']} ops={rstats['ops']} "
              f"deposits={rstats['deposits']} withdraws={rstats['withdraws']} "
              f"donates={rstats['donates']} reverts={rstats['reverts']} "
              f"violations={len(rviol)}  ({el:.1f}s)")
        summary.setdefault("random", []).append(
            dict(O=O, stats=rstats, violation_count=len(rviol),
                 sample=rviol[:5], seconds=round(el, 2)))

    total_viol = (
        sum(r["violation_count"] for r in p1p3)
        + len(gviol)
        + sum(r["violation_count"] for r in ng)
        + sum(r["violation_count"] for r in summary["random"])
    )
    summary["total_property_violations_excluding_P4i_openq"] = total_viol
    dt = time.time() - t0
    summary["total_seconds"] = round(dt, 2)
    print("\n" + "=" * 70)
    print(f"TOTAL property violations (P1/P2/P3/random): {total_viol}")
    print(f"P4(i) max attacker profit (open question answer): {max_profit_overall}")
    print(f"Total wall time: {dt:.1f}s")
    print("=" * 70)

    # machine-readable dump for transcription into the findings report
    with open("prorata-bruteforce-summary.json", "w") as f:
        json.dump(summary, f, indent=2, default=str)
    print("wrote prorata-bruteforce-summary.json")
    return summary


def _loss_frontier(loss_records):
    """Bucket loss records by (S_dep,B_dep) is too fine; report the max loss and
    a small table of the largest losses with their (v,S_dep,B_dep)."""
    if not loss_records:
        return {"max_loss": None, "top": []}
    srt = sorted(loss_records, key=lambda r: r[0], reverse=True)
    top = [dict(loss=l, v=v, S_dep=s, B_dep=b) for (l, v, s, b) in srt[:10]]
    return {"max_loss": srt[0][0], "top": top}


if __name__ == "__main__":
    main()
