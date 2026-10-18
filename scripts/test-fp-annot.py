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

print(f"fp_annot checks: {COUNT} passed")
