#!/usr/bin/env python3
"""Generate the Curve U0 balance tables (untrusted; the kernel decides each one).

For a certified coin runtime this reads the write-site producer's root sites at
the coin's balance base slot and writes `Blanc/Lift/CurveCoins/<Name>.lean`: a
table of the sites that may touch a balance entry, each with the path the table
reads it as, and a kernel decision that the table is exactly
`mappingSites base (wsRoot ann)`.  A site of an unlisted selector or shape stops
the generator: that is the U0 stop condition, not something to classify here.

Usage: balance_table.py [--write] [--md OUT] [--only NAME]
Default mode byte-compares the generated module with the committed one.
It also reconciles the certificate's SSTORE pcs with a linear decode of the
runtime before compiler metadata and prints any difference.
"""
import argparse
import contextlib
import io
import json
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[3]
sys.path[:0] = [str(ROOT / "scripts/lift"), str(ROOT / "scripts")]
import keccak  # noqa: E402
import symcore  # noqa: E402
import ws_annot  # noqa: E402

AUTH = "scripts/lift/certificates.json"
CAND = "scripts/reference/curve-u0/certificates.json"
MASK = ('const', 0xffffffffffffffffffffffffffffffffffffffff)
CD4 = ('op2', 'and', ('cd', ('const', 4)), MASK)
CD24 = ('op2', 'and', ('cd', ('const', 0x24)), MASK)
CALLER = ('op2', 'and', ('caller',), MASK)
SELF = ('op2', 'and', ('self',), MASK)
RAW_CALLER = ('caller',)


def sel(sig):
    return int.from_bytes(keccak.selector(sig), "big")


def H(): return '.holder'
def R(): return '.recipient'
def A(): return '.allowance'
def S(): return '.signed'
def O(role): return f'(.operator "{role}")'
def I(): return '.initializer'
def U(why): return f'(.unresolved "{why}")'


# (signature, {key term or 'top': path}).  Every path reads the source named in
# the U0 evidence; only the shape is kernel-checked (BalanceRow.shapeOk).
USDC_COMMON = {
    "transfer(address,uint256)": {CALLER: H(), RAW_CALLER: H(), CD4: R()},
    "transferFrom(address,address,uint256)": {CD4: A(), CD24: R()},
    "mint(address,uint256)": {CD4: O("minter")},
    "burn(uint256)": {RAW_CALLER: H(), CALLER: H()},
    "transferWithAuthorization(address,address,uint256,uint256,uint256,bytes32,uint8,bytes32,bytes32)": {CD4: S(), CD24: R()},
    "initialize(string,string,string,uint8,address,address,address,address)": {'top': U("initialize string copy; excluded only by the initialized flag")},
    "initializeV2(string)": {'top': U("initializeV2 string copy; excluded only by the initialized version")},
}
USDC_V21 = dict(USDC_COMMON, **{
    "receiveWithAuthorization(address,address,uint256,uint256,uint256,bytes32,uint8,bytes32,bytes32)": {CD4: S(), CD24: R()},
    "initializeV2_1(address)": {SELF: I(), CD4: I()},
})
USDC_V22 = dict(USDC_V21, **{
    "transferWithAuthorization(address,address,uint256,uint256,uint256,bytes32,bytes)": {CD4: S(), CD24: R()},
    "receiveWithAuthorization(address,address,uint256,uint256,uint256,bytes32,bytes)": {CD4: S(), CD24: R()},
    "blacklist(address)": {CD4: O("blacklister: packed word, high bit")},
    "unBlacklist(address)": {CD4: O("blacklister: packed word, high bit")},
    "initializeV2_2(address[],string)": {'top': U("initializeV2_2: string copy and the listed accounts' packed words; excluded only by the initialized version")},
})
DAI = {
    "transfer(address,uint256)": {CALLER: H(), RAW_CALLER: H(), CD4: R()},
    "transferFrom(address,address,uint256)": {CD4: A(), CD24: R()},
    "mint(address,uint256)": {CD4: O("ward")},
    "burn(address,uint256)": {CD4: A()},
    "push(address,uint256)": {CALLER: H(), RAW_CALLER: H(), CD4: R()},
    "pull(address,uint256)": {CD4: A(), CALLER: H(), RAW_CALLER: H()},
    "move(address,address,uint256)": {CD4: A(), CD24: R()},
}
USDT = {
    "transfer(address,uint256)": {CALLER: H(), CD4: R(), 'top': U("fee credit to balances[owner], a word read from slot 0")},
    "transferFrom(address,address,uint256)": {CD4: A(), CD24: R(), 'top': U("fee credit to balances[owner], a word read from slot 0")},
    "issue(uint256)": {'top': U("owner issue: credit to balances[owner], a word read from slot 0")},
    "redeem(uint256)": {'top': U("owner redeem: debit of balances[owner], a word read from slot 0")},
    "destroyBlackFunds(address)": {CD4: O("owner")},
}

COINS = {
    "Usdt": dict(reg=CAND, row="curve-u0-usdt", base=2, cert="Blanc.Lift.Usdt", ws="Blanc.Lift.UsdtWs",
                 imp="Blanc.Lift.UsdtWs", wscert="Blanc.Lift.Usdt.usdt_wsCert", table=USDT),
    "Dai": dict(reg=CAND, row="curve-u0-dai", base=2, cert="Blanc.Lift.Dai", ws="Blanc.Lift.DaiWs",
                imp="Blanc.Lift.DaiWs", wscert="Blanc.Lift.Dai.dai_wsCert", table=DAI),
    "UsdcV2": dict(reg=AUTH, row="usdc-impl-v2", base=9, cert="Blanc.Lift.Usdc.ImplV2", ws="Blanc.Lift.Usdc.ImplV2Ws",
                   imp="Blanc.Lift.Usdc.ImplV2Ws", wscert="Blanc.Lift.Usdc.implV2_wsCert", table=USDC_COMMON),
    "UsdcV2_1": dict(reg=AUTH, row="usdc-impl-v2_1", base=9, cert="Blanc.Lift.Usdc.ImplV2_1", ws="Blanc.Lift.Usdc.ImplV2_1Ws",
                     imp="Blanc.Lift.Usdc.ImplV2_1Ws", wscert="Blanc.Lift.Usdc.implV2_1_wsCert", table=USDC_V21),
    "UsdcV2_2": dict(reg=AUTH, row="usdc-impl", base=9, cert="Blanc.Lift.Usdc.Impl", ws="Blanc.Lift.Usdc.ImplWs",
                     imp="Blanc.Lift.Usdc.ImplWs", wscert="Blanc.Lift.Usdc.impl_wsCert", table=USDC_V22),
}


def root_checker(spec):
    rows = json.loads((ROOT / spec["reg"]).read_text())["certificates"]
    row = next(r for r in rows if r["id"] == spec["row"])
    with contextlib.redirect_stdout(io.StringIO()):
        entries, trees, effects, lean_reg, step_inst = symcore.load_cert(row)
    symcore.check_alignment(entries, ROOT / row["cert"])
    checker = ws_annot.Checker(entries, trees, effects, lean_reg, step_inst)
    checker.infer(max_rounds=200)
    checker.fill_missing()
    checker.rebase()
    errors = checker.check()
    if errors:
        raise SystemExit(f"{spec['row']}: self-check rejected {errors[:3]}")
    return row, checker, entries, trees


def children(u):
    for k in ("sub", "fall", "taken", "continuation"):
        if k in u:
            yield u[k]


def stores_from(u, trees, seen_entries, out):
    """SSTORE pcs in a subtree and every entry it can reach."""
    stack = [u]
    while stack:
        u = stack.pop()
        if u["kind"] == "next" and int(u["op"], 16) == 0x55:
            out.add(u["pc"])
        t = u.get("target_entry")
        if t is not None and t >= 0 and t not in seen_entries:
            seen_entries.add(t)
            stack.append(trees[t])
        stack.extend(children(u))


def selector_starts(trees):
    """Dispatcher arms: PUSH4 sel, EQ, ..., the next branch's taken side."""
    arms = {}

    def walk(u, pending, seen):
        while True:
            k = u["kind"]
            if k == "next":
                if int(u["op"], 16) == 0x63:
                    s = u["sub"]
                    if s["kind"] == "next" and int(s["op"], 16) in (0x14,):
                        pending = int(u["data"], 16)
                    elif s["kind"] == "next" and int(s["op"], 16) in (0x81, 0x82, 0x90) and \
                            s["sub"]["kind"] == "next" and int(s["sub"]["op"], 16) == 0x14:
                        pending = int(u["data"], 16)
                u = u["sub"]
            elif k == "dest":
                u = u["sub"]
            elif k == "branch":
                if pending is not None:
                    arms[pending] = u["taken"]
                    pending, u = None, u["fall"]
                else:
                    walk(u["taken"], None, seen)
                    u = u["fall"]
            elif k == "branchTo":
                if pending is not None:
                    arms[pending] = trees[u["target_entry"]]
                    pending = None
                else:
                    t = u["target_entry"]
                    if t not in seen:
                        seen.add(t)
                        walk(trees[t], None, seen)
                u = u["fall"]
            elif k == "jump" or k == "join":
                t = u["target_entry"]
                if t in seen:
                    return
                seen.add(t)
                u = trees[t]
            else:
                return

    walk(trees[0], None, {0})
    return arms


def linear_sstores(row):
    text = (ROOT / row["input"]["hex"]).read_text().strip().removeprefix("0x")
    b = bytes.fromhex(text)
    # solc metadata: CBOR tail whose length is the last two bytes
    end = len(b) - 2 - int.from_bytes(b[-2:], "big")
    if not 0 < end < len(b) or b[end] not in (0xa1, 0xa2, 0xa3):
        end = len(b)
    pcs, i = set(), 0
    while i < end:
        op = b[i]
        if op == 0x55:
            pcs.add(i)
        i += 1 + (op - 0x5f if 0x60 <= op <= 0x7f else 0)
    return pcs


def generate(name, spec):
    row, checker, entries, trees = root_checker(spec)
    base = spec["base"]
    table = {sel(s): (s, m) for s, m in spec["table"].items()}
    arms = selector_starts(trees)
    obs_by_pc = {}
    for _k, pc, obs in checker.stores:
        obs_by_pc.setdefault(pc, set()).add(obs[0])
    rows, problems = [], []
    # the certified order is the one the annotation file holds (lean_wret)
    root = sorted(checker.get_ret_e(0).sites, key=ws_annot.lean_site)
    for s in root:
        slot, guards, non_inc = s
        known = ws_annot.known(slot)
        hit = not known or (slot[0] == 'kecc' and slot[2] == ('const', base))
        if not hit:
            continue
        keys = [g[1] for g in guards]
        selector = next((c for c in keys if c <= 0xffffffff), None)
        if selector not in table:
            problems.append(f"unlisted selector for site {ws_annot.show_site(s)}")
            continue
        signature, reading = table[selector]
        key = 'top' if not known else slot[1]
        if key not in reading:
            problems.append(f"unlisted key under {signature}: {ws_annot.show_site(s)}")
            continue
        seen, out = set(), set()
        if selector in arms:
            stores_from(arms[selector], trees, seen, out)
        pcs = sorted(p for p in out if any(
            t[0] in ('top', 'arg') or (t[0] == 'kecc' and t[2] == ('const', base)) or t[0] == 'kecc1'
            for t in obs_by_pc.get(p, ())))
        rows.append((reading[key], s, signature, selector, pcs))
    return row, checker, trees, rows, problems


def emit(name, spec, rows):
    ws = spec["ws"]
    title = spec["row"]
    lines = [
        f"import {spec['imp']}",
        "import Blanc.Lift.WriteSiteMapping",
        "",
        f"/-! GENERATED by scripts/reference/curve-u0/balance_table.py -- do not edit.",
        f"The sites of `{title}` that may touch a balance entry (base slot {spec['base']}). The kernel decides that",
        "the table is exactly `mappingSites` over the certified root, and each row's shape. The paths are",
        "the table's reading of the source; only the shape is checked. Curve 3pool U0 candidate. -/",
        "",
        f"namespace Blanc.Lift.CurveCoins.{name}",
        "",
        "open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace",
        "",
        "/-- The balance table. -/",
        "def balanceTable : List BalanceRow :=",
        "  [" + ",\n   ".join(f"⟨{p}, {ws_annot.lean_site(s)}⟩" for p, s, *_ in rows) + "]",
        "",
        "/-- The table is exactly the certified root's sites that may touch a balance entry. -/",
        f"theorem balanceTable_exact :",
        f"    mappingSites {spec['base']} (wsRoot {ws}.implWsAnn) = balanceTable.map BalanceRow.site := by",
        "  decide +kernel",
        "",
        "/-- Each row's reading fits its site's shape. -/",
        f"theorem balanceTable_shapes : balanceTable.all (BalanceRow.shapeOk {spec['base']}) = true := by",
        "  decide +kernel",
        "",
        "/-- **Every successful store of this code** meets a table row (read through",
        "`balanceTable_exact`) or a known slot of another shape. -/",
        "theorem store_table_or_other {root node : Exec.Deriv} (pc : root.pc = 0)",
        f"    (hcode : root.sevm.code = {spec['cert']}.code)",
        "    (stateGas : root.sevm.benvStat.rules.stateGas = none)",
        "    (chain : Exec.Deriv.ParentPrefix root node)",
        "    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :",
        f"    ∃ site ∈ wsRoot {ws}.implWsAnn,",
        "      (∀ guard ∈ site.guards, guard.1.Den (Env.root root.sevm) guard.2) ∧",
        "      (site.nonInc = true →",
        "        write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat) ∧",
        "      (site ∈ balanceTable.map BalanceRow.site ∧ site.slot.Den (Env.root root.sevm) write.key ∨",
        f"        site.slot.known = true ∧ mappingKey? {spec['base']} site.slot = none ∧",
        "          write.key = site.slot.eval (Env.root root.sevm)) := by",
        "  rw [← balanceTable_exact]",
        f"  exact successfulSstore_mappingSite {spec['base']} {spec['cert']}.cert_check {spec['wscert']} pc hcode stateGas chain found",
        "",
        f"end Blanc.Lift.CurveCoins.{name}",
        "",
    ]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--md", default=None)
    ap.add_argument("--only", action="append")
    args = ap.parse_args()
    md, bad = [], 0
    for name, spec in COINS.items():
        if args.only and name not in args.only:
            continue
        if not (ROOT / "Blanc/Lift" / spec["ws"].removeprefix("Blanc.Lift.").replace(".", "/") / "Ann.lean").exists():
            print(f"{name}: no certified annotation on this branch; skipped")
            continue
        row, checker, trees, rows, problems = generate(name, spec)
        for p in problems:
            print(f"STOP {name}: {p}")
            bad += 1
        if problems:
            continue
        text = emit(name, spec, rows)
        path = ROOT / f"Blanc/Lift/CurveCoins/{name}.lean"
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            print(f"WROTE {path.relative_to(ROOT)} ({len(rows)} rows)")
        elif not path.exists() or path.read_text() != text:
            print(f"FAIL {name}: {path.relative_to(ROOT)} differs from its regeneration")
            bad += 1
        else:
            print(f"ok   {name}: {len(rows)} rows, byte-identical")
        cert_pcs = set()
        for t in trees.values():
            stores_from(t, trees, set(trees), cert_pcs)
        lin = linear_sstores(row)
        print(f"     {name}: {len(cert_pcs)} SSTORE pcs in the certificate, {len(lin)} linear before metadata; "
              f"linear-only {[hex(p) for p in sorted(lin - cert_pcs)]}; cert-only {[hex(p) for p in sorted(cert_pcs - lin)]}")
        md.append(f"\n### {name} (base slot {spec['base']})\n\n| Function | Selector | Certified root site key | nonInc | Reading | SSTORE pcs on the selector at this base or `top` |\n|---|---|---|---|---|---|")
        for p, s, sig, selector, pcs in rows:
            slot, _g, ni = s
            key = 'top' if not ws_annot.known(slot) else ws_annot.show_term(slot[1])
            md.append(f"| `{sig.split('(')[0]}` | `0x{selector:08x}` | `{key.replace('0xffffffffffffffffffffffffffffffffffffffff', 'MASK')}` | {'yes' if ni else 'no'} | {p.strip('().')} | {', '.join(hex(x) for x in pcs)} |")
    if args.md:
        Path(args.md).write_text("\n".join(md) + "\n")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
