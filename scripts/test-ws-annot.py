#!/usr/bin/env python3
"""Focused checks for the write-site annotation producer's mirror of the
goal-branch `wsNode` (`scripts/lift/ws_annot.py`, checked by
`Blanc/Lift/WriteSite.lean`'s `wsCert`); no Lean invocation.

Covers the provenance transfer (`mkOp2` folding and absorption, `subst`),
the `wstep` arms (push, keeps guard, SSTORE coverage, SLOAD naming, EQ
guards, keccak shapes, SUB facts), the goal-branch gates (`.ret` top rule,
`.jump`/`.branchTo` `gotoCompat` and return-summary equality, `callNext`
parameter-state/arity/keeps/coverage/continuation rules), the union-find
entry-word assignment (pins, propagation, conflict reporting), and the
negative-canonical rebase (valid naturals, preserved `compat` verdicts).

The producer's own per-entry self-check exercises these arms over all 180
USDC entries; this file pins their accept/reject boundary on synthetic
states and trees.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts" / "lift"))
import ws_annot
from ws_annot import (
    Checker, WSt, WRet, INIT, TOP, Reject,
    known, mk_op2, term_subst, show_term,
    wst_param, prov_of, compat_w, site_covers, site_of,
    wstep, refine_w, popped_w, eq_guard, inst_site, resume_w, ret_ok,
    resolve_args, lean_term, lean_site, lean_b256,
)
from symcore import goto_compat, ninst_kind

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


def RMARK():
    return ('ret',)


def C(v):
    return ('const', v)


def A(*names):
    return list(names)


CALLER = ('caller',)
SELF = ('self',)
M = 2 ** 256


def R0(sites=(), keeps=False):
    return WRet((), frozenset(), keeps, frozenset(sites))


# -- Term: constant folding, absorption, commutativity --
require(mk_op2('add', ('const', 1), ('const', 2)) == ('const', 3), "add folds")
require(mk_op2('sub', ('const', 1), ('const', 2)) == ('const', M - 1),
        "sub wraps mod 2^256")
require(mk_op2('div', ('const', 7), ('const', 0)) == ('const', 0),
        "div by zero is zero")
require(mk_op2('shl', ('const', 256), ('const', 1)) == ('const', 0),
        "shl past the width is zero")
require(mk_op2('shr', ('const', 255), ('const', 2 ** 255)) == ('const', 1),
        "shr folds")
require(mk_op2('exp', ('const', 2), ('const', 255)) == ('const', 2 ** 255),
        "exp folds")
require(mk_op2('add', TOP, ('const', 1)) == TOP, "top absorbs left")
require(mk_op2('add', ('const', 1), TOP) == TOP, "top absorbs right")
require(mk_op2('add', ('const', 1), CALLER)
        == ('op2', 'add', CALLER, ('const', 1)), "commutative const goes right")
require(mk_op2('sub', ('const', 1), CALLER)
        == ('op2', 'sub', ('const', 1), CALLER), "non-comm const stays left")
require(mk_op2('and', ('op2', 'and', CALLER, ('const', 5)), ('const', 5))
        == ('op2', 'and', CALLER, ('const', 5)), "re-masking is identity")
require(mk_op2('and', ('op2', 'and', CALLER, ('const', 5)), ('const', 6))
        == ('op2', 'and', ('op2', 'and', CALLER, ('const', 5)), ('const', 6)),
        "different mask keeps both")
require(not known(TOP) and known(CALLER)
        and not known(('cd', TOP)) and known(('cd', CALLER)),
        "known")
require(term_subst(('arg', 1), [CALLER, SELF]) == SELF, "subst arg")
require(term_subst(('arg', 9), [CALLER]) == TOP, "subst arg out of range")
require(term_subst(('kecc', ('arg', 0), ('const', 3)), [CALLER])
        == ('kecc', CALLER, ('const', 3)), "subst kecc")
require(term_subst(('kecc', ('arg', 0), ('arg', 9)), [CALLER]) == TOP,
        "subst kecc collapses to top")
require(term_subst(('op2', 'add', ('const', 2), ('const', 3)), []) == ('const', 5),
        "subst folds constants")

# -- ninst classification (shared core) --
require(ninst_kind(0x60, {}) == ('push',), "push")
require(ninst_kind(0x80, {}) == ('dup',), "dup")
require(ninst_kind(0x90, {}) == ('swap',), "swap")
require(ninst_kind(0x33, {0x33: '.reg .caller'}) == ('reg', 'caller'), "caller")
require(ninst_kind(0xf4, {0xf4: '.exec .delegatecall'})
        == ('exec', 'delegatecall'), "delegatecall")
rejects(lambda: ninst_kind(0xf0, {}), "no Ninst", "CREATE unliftable")

# -- gotoCompat (shared core) --
require(goto_compat([C(5)], [U()]) is True, "const/unk")
require(goto_compat([RMARK()], [RMARK()]) is True, "ret/ret")
require(goto_compat([U()], [RMARK()]) is False, "unk/ret")

# -- wstep: push records provenance and bounds --
st = wstep(R0(), 0x60, b'\x03', ('push',), None, INIT, 0)
require(st.kv == (1,) and prov_of(st, 1) == ('const', 3), "push prov")
require(('bnd', 1, 3, 3) in st.facts, "push bound")

# -- wstep: keeps guard --
rejects(lambda: wstep(R0(keeps=True), 0x55, b'', ('reg', 'sstore'), [],
                      WSt((1, 2), (), frozenset(), (), (), (), (), (), ()), 0),
        "keeping function", "sstore in keeping function")

# -- wstep: SSTORE coverage gate --
bare2 = WSt((1, 2), (), frozenset(),
            ((1, ('const', 5)),), (), (), (), (), ())
rejects(lambda: wstep(R0(), 0x55, b'', ('reg', 'sstore'), [], bare2, 0x10),
        "no listed site", "uncovered SSTORE")
listed = (('const', 5), (), False)
st = wstep(WRet((), frozenset(), False, frozenset({listed})), 0x55, b'',
           ('reg', 'sstore'), [], bare2, 0x10)
require(st.cur == () and st.ub == (), "store forgets storage values")
require(any(site_covers(s, site_of(bare2, 1, 2)) for s in
            WRet((), frozenset(), False, frozenset({listed})).sites),
        "listed covers observed")

# -- wstep: SLOAD names the current value's symbol --
loaded = WSt((8,), (), frozenset(), ((8, ('const', 5)),), (),
             ((9, ('const', 5)),), (), (), ())
st = wstep(R0(), 0x54, b'', ('reg', 'sload'), [None], loaded, 0x20)
require(st.kv == (9,), "sload reuses the current value symbol")

# -- wstep: EQ feeds refine guards --
eq_st = WSt((1, 2), (), frozenset(),
            ((1, CALLER), (2, ('const', 0x1234))), (), (), (), (), ())
st = wstep(R0(), 0x14, b'', ('reg', 'eq'), [None], eq_st, 0x30)
r = st.kv[0]
g = refine_w(st, r, [], False)
require((CALLER, 0x1234) in g.guards, "nonzero EQ learns the guard")
require(refine_w(st, r, [], True).guards == (), "zero arm learns no guard")
require(eq_guard(CALLER, ('const', 7)) == (CALLER, 7), "eqGuard")
require(eq_guard(CALLER, SELF) is None, "eqGuard needs a const side")

# -- wstep: keccak256 over constant memory builds kecc shapes --
mem_st = WSt((10, 11), (), frozenset(),
             ((10, ('const', 0)), (11, ('const', 64)),
              (20, CALLER), (21, ('const', 3))),
             ((0, 20), (32, 21)), (), (), (), ())
st = wstep(R0(), 0x20, b'', ('reg', 'keccak256'), [None], mem_st, 0x40)
require(prov_of(st, st.kv[0]) == ('kecc', CALLER, ('const', 3)),
        "two-word hash shape")
mem_st1 = WSt((10, 11), (), frozenset(),
              ((10, ('const', 0)), (11, ('const', 32)), (20, CALLER)),
              ((0, 20),), (), (), (), ())
st = wstep(R0(), 0x20, b'', ('reg', 'keccak256'), [None], mem_st1, 0x40)
require(prov_of(st, st.kv[0]) == ('kecc1', CALLER), "one-word hash shape")

# -- wstep: symbolic SUB below its minuend --
sub_st = WSt((1, 2), (), frozenset({('le', 2, 1)}),
             (), (), ((1, ('const', 9)),), (), (), ())
st = wstep(R0(), 0x03, b'', ('reg', 'sub'), [None], sub_st, 0x50)
r = st.kv[0]
require(('le', r, 1) in st.facts, "sub learns le")
require((r, ('const', 9)) in st.ub, "sub inherits the minuend bound")

# -- wstep: constant MSTORE tracks the word, then MLOAD-side maps keep it --
m_st = WSt((1, 2), (), frozenset(),
           ((1, ('const', 0)), (2, CALLER)), (), (), (), (), ())
st = wstep(R0(), 0x52, b'', ('reg', 'mstore'), [], m_st, 0x60)
require((0, 2) in st.mem, "constant mstore records the word")

# -- compat: ub may be met by cur; prov must match; args lengths must match --
A = WSt((1,), (-1,), frozenset(), (), (), (), ((1, CALLER),), (), ())
S = WSt((5,), (9,), frozenset(), (), (), ((5, CALLER),), (), (), ())
require(compat_w(S, A) is None, "ub met by cur")
A2 = WSt((1,), (-1,), frozenset(), ((1, SELF),), (), (), (), (), ())
require(compat_w(S, A2) is not None, "prov mismatch")
A3 = WSt((1,), (-1, -2), frozenset(), (), (), (), (), (), ())
require(compat_w(S, A3) == "args length", "args length")
require(compat_w(WSt((1, 2), (), frozenset(), (), (), (), (), (), ()),
                 WSt((1,), (), frozenset(), (), (), (), (), (), ()))
        == "length", "kv length")

# -- instSite substitutes caller terms and filters unknown guards --
s = (('kecc', ('arg', 0), ('arg', 1)), [(('arg', 2), 7)], False)
require(inst_site([CALLER, SELF], [], s)
        == (('kecc', CALLER, SELF), (), False),
        "instSite drops guards that substitute to top")
require(inst_site([TOP], [(SELF, 1)], s)
        == (TOP, ((SELF, 1),), False),
        "instSite drops unknown instantiated guards")

# -- resolve_args: pins propagate, conflicts reported --
entries = [(0, [], 0), (0, [U()] * 3, 0), (0, [U()] * 4, 0)]
trees = {0: {'kind': 'jump', 'pc': 0, 'target_entry': 1},
         1: {'kind': 'last', 'pc': 1, 'op': '0x0'},
         2: {'kind': 'jump', 'pc': 2, 'target_entry': 1}}
argmap, conflicts, _ = resolve_args(entries, trees, {1, 2})
require(len(conflicts) == 1 and conflicts[0][1] == [0, 1, 2],
        "conflict set reported")
require(argmap[0] == argmap[1] == argmap[2] == (),
        "first pin wins for every member")
argmap2, conflicts2, _ = resolve_args(entries, trees, {1})
require(len(conflicts2) == 1 and conflicts2[0][2] == [(), (1, 2, 3)],
        "dispatcher pin conflicts with a called jump target")
argmap3, conflicts3, _ = resolve_args(entries, trees, set())
require(conflicts3 == [] and argmap3[0] == argmap3[1] == argmap3[2] == (),
        "unpinned sets take empty entry words")


def checker(entries, trees):
    def no_step(*args):
        raise AssertionError("step_inst called")
    return Checker(entries, trees, {}, {}, no_step)


# -- .ret top rule and summary check --
entries = [(0, [], 0)]
ret_tree = {0: {'kind': 'ret', 'pc': 0}}
c = checker(entries, ret_tree)
c.ann = {0: INIT}
c.mode = 'check'
RS = WRet([], frozenset(), False, frozenset())
c.walk(ret_tree[0], [RMARK()], WSt((7,), (), frozenset(), (), (), (), (), (), ()),
       RS, 0)
require(True, "ret with ret top accepted")
rejects(lambda: c.walk(ret_tree[0], [U()], WSt((7,), (), frozenset(), (), (),
                                               (), (), (), ()),
                        RS, 0),
        "top not ret", "ret with unk top")
R1 = WRet([CALLER], frozenset(), False, frozenset())
rejects(lambda: c.walk(ret_tree[0], [RMARK()],
                        WSt((7, 8), (), frozenset(), (), (), (), (), (), ()),
                        R1, 0),
        "prov", "ret against foreign summary")

# -- .jump gotoCompat gate --
entries = [(0, [], 0), (0x100, [C(7)], 0)]
jump_tree = {0: {'kind': 'jump', 'pc': 0, 'target_entry': 1},
             1: {'kind': 'last', 'pc': 1, 'op': '0x0'}}
c = checker(entries, jump_tree)
c.ann = {0: INIT, 1: WSt((5,), (), frozenset({('bnd', 5, 7, 7)}), (), (),
                         (), (), (), ())}
c.mode = 'check'
c.walk(jump_tree[0], [C(0x100), C(7)],
       WSt((3, 5), (), frozenset({('bnd', 5, 7, 7)}), (), (), (), (), (), ()),
       RS, 0)
require(True, "jump with matching frame accepted")
rejects(lambda: c.walk(jump_tree[0], [C(0x100), C(8)],
                        WSt((3, 5), (), frozenset({('bnd', 5, 8, 8)}), (), (),
                            (), (), (), ()),
                        RS, 0),
        "gotoCompat", "jump with mismatching frame")

# -- .branchTo needs the target frame and the same return summary --
entries = [(0, [], 0), (0x200, [C(7)], 0)]
fall = {'kind': 'last', 'pc': 1, 'op': '0x0'}
bt_tree = {0: {'kind': 'branchTo', 'pc': 0, 'fall': fall, 'target_entry': 1},
           1: {'kind': 'last', 'pc': 2, 'op': '0x0'}}
c = checker(entries, bt_tree)
c.ann = {0: INIT, 1: WSt((), (), frozenset(), (), (), (), (), (), ())}
c.mode = 'check'
c.comp = {0: 0, 1: 1}
c.comp_n = {0: 0, 1: 1}
c.ret_prov = {0: (), 1: (CALLER,)}
c.ret_les = {0: frozenset(), 1: frozenset()}
c.sites = {0: set(), 1: set()}
c.keeps = {0: True, 1: True}
rejects(lambda: c.walk(bt_tree[0], [C(0x200), C(1), C(7)],
                        WSt((4, 5), (), frozenset({('bnd', 5, 1, 1)}), (), (),
                            (), (), (), ()),
                        RS, 0),
        "return summary differs", "branchTo across summaries")
c.comp = {0: 0, 1: 0}
c.walk(bt_tree[0], [C(0x200), C(1), C(7)],
       WSt((4, 5), (), frozenset({('bnd', 5, 1, 1)}), (), (), (), (), (), ()),
       RS, 0)
require(True, "branchTo with matching frame accepted")

# -- .callNext: parameter-state, arity, keeps, coverage, continuation --
entries = [(0, [], 0), (0x100, [U(), RMARK()], 1)]
cont = {'kind': 'dest', 'pc': 9,
        'sub': {'kind': 'last', 'pc': 10, 'op': '0x0'}}
call_tree = {0: {'kind': 'callNext', 'pc': 0, 'target_entry': 1,
                 'continuation': cont},
             1: {'kind': 'last', 'pc': 2, 'op': '0x0'}}
c = checker(entries, call_tree)
c.ann = {0: INIT, 1: wst_param(2)}
c.mode = 'check'
Rc = WRet([TOP], frozenset(), False, frozenset())
c.ret_prov = {c.comp[1]: Rc.prov}
c.ret_les = {c.comp[1]: Rc.les}
c.sites = {c.comp[1]: set()}
c.keeps = {c.comp[0]: False, c.comp[1]: False}
caller = WSt((8, 9, 10), (), frozenset(), (), (), (), (), (), ())
c.walk(call_tree[0], [C(0x100), C(1), C(0x200)], caller,
       WRet((), frozenset(), False, frozenset()), 0)
require(True, "callNext with param entry accepted")
rejects(lambda: c.walk(call_tree[0], [C(0x100), C(1), C(0x200)], caller,
                        WRet((), frozenset(), True, frozenset()), 0),
        "does not keep", "call into non-keeping callee from keeper")
c2 = checker(entries, call_tree)
c2.ann = {0: INIT, 1: WSt((1, 2), (1, 2), frozenset(), (), (), (), (), (), ())}
c2.mode = 'check'
rejects(lambda: c2.walk(call_tree[0], [C(0x100), C(1), C(0x200)], caller,
                         WRet((), frozenset(), False, frozenset()), 0),
        "not the callee parameter state", "call into non-param entry")
rejects(lambda: c.walk(call_tree[0], [C(0x100), C(1), U()], caller,
                        WRet((), frozenset(), False, frozenset()), 0),
        "continuation not constant", "call with unknown return address")

# -- canon uses negative entry-word indices; rebase restores naturals --
st = WSt((5, 6), (5, 7), frozenset({('le', 5, 7)}),
         ((5, CALLER), (7, SELF)), (), (), (), (), ())
A = Checker.canon(st)
require(all(s < 0 for s in A.args), "canon names entry words negatively")
require(compat_w(st, A) is None, "self-compat of canon")
c3 = checker([(0, [], 0)], {0: {'kind': 'last', 'pc': 0, 'op': '0x0'}})
c3.ann = {0: A}
c3.rebase()
B = c3.ann[0]
require(all(s >= 0 for s in list(B.args) + [k for k, _ in B.prov]),
        "rebase restores naturals")
require(compat_w(st, B) is None, "compat preserved across rebase")

# -- resume names fresh returns above the caller --
sig = WSt((3, 4), (3,), frozenset(), ((3, CALLER),), (), (), (), (), ())
Rc2 = WRet([('arg', 0)], frozenset({(0, 0)}), True, frozenset())
st = resume_w(sig, [3], [4], Rc2, 1)
require(st.kv[0] not in (3, 4) and prov_of(st, st.kv[0]) == CALLER,
        "resume instantiates the return term")
require(('le', st.kv[0], 3) in st.facts, "resume instantiates order facts")

# -- emission shapes --
require(lean_b256(0) == "(Nat.toB256 0x0)", "b256 emission")
require(lean_term(('kecc', CALLER, ('const', 3)))
        == "(.kecc .caller (.const (Nat.toB256 0x3)))", "kecc emission")
require(lean_term(('op2', 'shr', ('const', 2), CALLER))
        == "(.op2 .shr (.const (Nat.toB256 0x2)) .caller)", "op2 emission")
require(lean_site((TOP, [], True)) == "⟨.top, [], true⟩", "site emission")

print(f"ws_annot checks: {COUNT} passed")
