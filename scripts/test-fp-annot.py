#!/usr/bin/env python3
"""Focused checks for the free-pointer annotation producer's mirror of the
goal-branch `fpNode` (`scripts/lift/fp_annot.py`, checked by
`Blanc/Lift/FreePtr.lean`'s `fpCert`); no Lean invocation.

Covers the soundness-fix arms: `.ret` requires the abstract stack to start
with `.ret`, and `.jump`/`.branchTo` require `gotoCompat` against the target
entry's declared frame before the old `compat` checks. The producer's own
per-entry self-check exercises these arms over all 180 USDC entries; this
file pins their accept/reject boundary on synthetic trees.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts" / "lift"))
import fp_annot
from fp_annot import Checker, FSt, Reject, goto_compat

COUNT = 0


def require(condition, label):
    global COUNT
    if not condition:
        raise AssertionError(label)
    COUNT += 1


def rejects(fn, fragment, label):
    global COUNT
    try:
        fn()
    except Reject as e:
        if fragment not in str(e):
            raise AssertionError(f"{label}: wrong reason: {e}")
        COUNT += 1
        return
    raise AssertionError(f"{label}: accepted, want reject ({fragment})")


def U():
    return ('unk',)


def R():
    return ('ret',)


def C(v):
    return ('const', v)


def checker(entries, trees):
    def no_step(*args):
        raise AssertionError("step_inst called")
    return Checker(entries, trees, {}, {}, no_step)


# -- gotoCompat (Blanc/Lift/Check.lean) --
require(goto_compat([], []) is True, "empty/empty")
require(goto_compat([U()], [U()]) is True, "unk/unk")
require(goto_compat([C(5)], [U()]) is True, "const/unk")
require(goto_compat([R()], [U()]) is True, "ret/unk")
require(goto_compat([C(5)], [C(5)]) is True, "const match")
require(goto_compat([C(5)], [C(6)]) is False, "const mismatch")
require(goto_compat([R()], [R()]) is True, "ret match")
require(goto_compat([U()], [R()]) is False, "unk/ret")
require(goto_compat([C(1)], [R()]) is False, "const/ret")
require(goto_compat([C(5)], []) is False, "stack longer")
require(goto_compat([], [C(5)]) is False, "frame longer")
require(goto_compat([C(5), R()], [C(5), R()]) is True, "two-word match")

# -- .ret top rule --
entries = [(0, [], 0)]
ret_tree = {0: {'kind': 'ret', 'pc': 0}}
c = checker(entries, ret_tree)
c.ann = {0: fp_annot.INIT}
c.mode = 'check'
c.walk(ret_tree[0], [R()], FSt((7,), frozenset(), None),
       FSt((), frozenset(), None), 0)
require(c.returns.get(c.comp[0]) == [FSt((), frozenset(), None)],
        "ret records popped state")
rejects(lambda: c.walk(ret_tree[0], [U()], FSt((7,), frozenset(), None),
                        FSt((), frozenset(), None), 0),
        "top not ret", "ret with unk top")
rejects(lambda: c.walk(ret_tree[0], [], FSt((7,), frozenset(), None),
                        FSt((), frozenset(), None), 0),
        "top not ret", "ret with empty stack")
rejects(lambda: c.walk(ret_tree[0], [R()], FSt((), frozenset(), None),
                        FSt((), frozenset(), None), 0),
        "empty frame", "ret with empty frame")
c.walk(ret_tree[0], [R()], FSt((7,), frozenset(), None),
       FSt((), frozenset(), None), 0)
require(True, "ret compat against matching summary accepted")
rejects(lambda: c.walk(ret_tree[0], [R()], FSt((7,), frozenset(), None),
                        FSt((0,), frozenset({('bnd', 0, 5, 5)}), None), 0),
        "length", "ret against longer summary")

# -- .jump gotoCompat gate --
entries = [(0, [], 0), (0x100, [C(7)], 0)]
jump_tree = {0: {'kind': 'jump', 'pc': 0, 'target_entry': 1},
             1: {'kind': 'last', 'pc': 1, 'op': '0x0'}}
c = checker(entries, jump_tree)
c.ann = {0: fp_annot.INIT, 1: FSt((9,), frozenset({('bnd', 9, 7, 7)}), None)}
c.ret = {}
c.mode = 'check'
c.walk(jump_tree[0], [C(0x100), C(7)], FSt((3, 5), frozenset({('bnd', 5, 7, 7)}), None),
       c.get_ret(c.comp[0]), 0)
require(True, "jump with matching frame accepted")
rejects(lambda: c.walk(jump_tree[0], [C(0x100), C(8)],
                        FSt((3, 5), frozenset({('bnd', 5, 8, 8)}), None),
                        c.get_ret(c.comp[0]), 0),
        "gotoCompat", "jump with mismatching frame")
rejects(lambda: c.walk(jump_tree[0], [],
                        FSt((3, 5), frozenset({('bnd', 5, 7, 7)}), None),
                        c.get_ret(c.comp[0]), 0),
        "empty abstract stack", "jump with empty stack")

# -- .branchTo gotoCompat gate (frame below target and condition) --
entries = [(0, [], 0), (0x200, [C(7)], 0)]
fall = {'kind': 'last', 'pc': 1, 'op': '0x0'}
bt_tree = {0: {'kind': 'branchTo', 'pc': 0, 'fall': fall, 'target_entry': 1},
           1: {'kind': 'last', 'pc': 2, 'op': '0x0'}}
c = checker(entries, bt_tree)
c.ann = {0: fp_annot.INIT, 1: FSt((), frozenset(), None)}
c.ret = {}
c.mode = 'check'
c.walk(bt_tree[0], [C(0x200), C(1), C(7)],
       FSt((4, 5), frozenset({('bnd', 5, 1, 1)}), None),
       c.get_ret(c.comp[0]), 0)
require(True, "branchTo with matching frame accepted")
rejects(lambda: c.walk(bt_tree[0], [C(0x200), C(1), C(8)],
                        FSt((4, 5), frozenset({('bnd', 5, 1, 1)}), None),
                        c.get_ret(c.comp[0]), 0),
        "gotoCompat", "branchTo with mismatching frame")

# -- compat maps annotation fp symbols to the incoming fp (not 0) --
A = FSt((0,), frozenset({('bnd', 1, 5, 9)}), 1)
require(fp_annot.compat(FSt((4,), frozenset({('bnd', 4, 5, 9)}), 4), A) is None,
        "fp fact renamed to incoming fp")
require(fp_annot.compat(FSt((4,), frozenset({('bnd', 4, 5, 9)}), None), A)
        == "free pointer unknown", "missing incoming fp")

# -- R1: the calldata `bytes` decoder check ISZERO(OR(GT(len, C), GT(..))) JUMPI --
# bounds len on the jump arm: the comparison chain survives closeLive through
# its consumed results, three learning rounds reach the GT, and the order fact
# learned is also stated as len's interval.
C32 = 2 ** 32
chain = frozenset({('bnd', 18, C32, C32), ('ltr', 19, 18, 11), ('bnd', 19, 0, 1),
                   ('ltr', 17, 13, 16), ('bnd', 17, 0, 1), ('orr', 20, 19, 17),
                   ('isz', 21, 20), ('bnd', 21, 0, 1)})
kept = fp_annot.close_live((21, 11, 13), None, chain)
require(('ltr', 19, 18, 11) in kept and ('bnd', 18, C32, C32) in kept,
        "closeLive keeps the comparison chain below a live result")
learned = fp_annot.refine_facts(kept, 21, False)
require(fp_annot.bnd2(learned, 11)[1] == C32, "jump arm bounds len by 2^32")
require(fp_annot.bnd2(fp_annot.close_live((11,), None, learned), 11)[1] == C32,
        "len's bound outlives the dead constant symbol")

# -- R1: CALL leaves return data below 2^160; RETURNDATASIZE reads the bound --
call = ('exec', 'call')
after = fp_annot.rds_keep(call, frozenset({('rds', 5)}))
require(after == frozenset({('rds', fp_annot.MEMCAP - 1)}), "CALL resets the bound")
require(fp_annot.rds_keep(('exec', 'staticcall'), after) == frozenset(),
        "other exec instructions forget it")
require(fp_annot.rds_eff(after, ('reg', 'returndatasize'), 9)
        == {('bnd', 9, 0, fp_annot.MEMCAP - 1)}, "RETURNDATASIZE is bounded")

# -- a store of a value not known good forgets the pointer (Lean: no rejection) --
fs0 = frozenset({('bnd', 1, 64, 64)})
require(fp_annot.mem_eff(fs0, 3, ('reg', 'mstore'), [1, 2], 0)[0] is None,
        "unbounded free-pointer store forgets fp")

# -- canonical annotations never alias the free pointer with a frame word --
st = FSt((4, 7), frozenset({('bnd', 4, 128, 256)}), 4)
cst = Checker.canon(st)
require(cst.fp is not None and cst.fp not in cst.kv
        and fp_annot.bnd2(cst.facts, cst.fp) == (128, 256),
        "canon gives fp its own symbol with its bounds")

print(f"fp_annot checks: {COUNT} passed")
