#!/usr/bin/env python3
"""Write-site annotations for a lift certificate (untrusted producer side).

Produces `Ann.lean` for `Blanc/Lift/WriteSite.lean` (`wsCert`): one `WAnn`
(entry state plus function summary) per certificate entry, in entry order.
The analysis mirrors `WriteSite.lean` (`wstep`, `provEff`, `memEff`,
`siteOf`, `refine`, `compat`, `instSite`, `resume`, `retOk`, `wsNode`) the
way `scripts/lift/fp_annot.py` mirrors `Blanc/Lift/FreePtr.lean`: it infers
one abstract frame state per entry by a fixpoint over the entry trees, then
re-walks every tree with the inferred annotations exactly as the Lean checker
does and reports the first rejection per entry, if any.

Nothing here is trusted. The Lean kernel decides
`wsCert Impl.cert implWsAnn` over the emitted annotations; a wrong annotation
is a failed build, never a wrong theorem.

Shares one symbolic core with the free-pointer producer (amendment A3): the
interval facts and the stack transfer live in `scripts/lift/symcore.py` and
are imported here. `WriteSite.lean` reuses `FreePtr`'s facts (`Fact`,
`entails`, `opFacts`, `refineFacts`) and the transfer discipline
(`ninstTransfer` on index patterns, `gotoCompat`), so those are shared;
everything else (`Term`, `WSt`, `WRet`, `Site`, `wstep`'s provenance and
memory maps, `compat`, `resume`, the fixpoint over summaries) is
write-site-specific and lives here.

Entries and trees are computed by `scripts/lift/lift.py` itself (run
in-process with the registry row's arguments; no copies of its pipeline),
and `ninstTransfer` on index patterns is reused from `lockann.py`
(`labels`) rather than reimplemented.
"""

import json
import sys
import time
from pathlib import Path
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[2]
sys.path.insert(0, str(SCRIPT.parent))
import lockann
from symcore import (
    MAXW, Reject, bnd2, entails, op_facts, refine_facts, goto_compat,
    ninst_kind,
    WIDEN_AFTER, widen_hull, components, comp_rets,
    load_cert, check_alignment,
)
from symcore import syms as fact_syms, rename as srename
from symcore import bnd2 as sbnd2, bnd_of as sbnd_of

M = 2 ** 256  # B256 arithmetic is modulo 2^256 (Jaune Basic.lean)


def b256_add(x, y):
    return (x + y) % M


def b256_sub(x, y):
    return (x - y) % M


def b256_mul(x, y):
    return (x * y) % M


def b256_div(x, y):
    return 0 if y == 0 else x // y  # Jaune B256.divMod: division by zero is 0


def b256_shl(x, y):
    # Op2.eval .shl x y = y <<< x.toNat (x is the top operand): shift the
    # second word left by the first (Jaune B256.shiftLeft).
    return 0 if x >= 256 else (y << x) % M


def b256_shr(x, y):
    # Op2.eval .shr x y = y >>> x.toNat: shift the second word right.
    return 0 if x >= 256 else y >> x


def b256_exp(x, y):
    return pow(x, y, M)  # Jaune B256.bexp via Nat.powMod


OP2_EVAL = {'add': b256_add, 'sub': b256_sub, 'mul': b256_mul,
            'div': b256_div, 'and': lambda x, y: x & y,
            'or': lambda x, y: x | y, 'shl': b256_shl, 'shr': b256_shr,
            'exp': b256_exp}
# Op2.ofRinst (WriteSite.lean): exactly these nine record provenance.
OP2_REG = set(OP2_EVAL)
# Op2.comm: a constant operand is kept on the right.
OP2_COMM = {'add', 'mul', 'and', 'or'}

# Provenance terms (WriteSite.Term) as tuples: ('top',) ('caller',)
# ('self',) ('cd', t) ('const', c) ('arg', i) ('op2', o, a, b)
# ('kecc', a, b) ('kecc1', t). B256 values are Python ints.
TOP = ('top',)

# Prototype of the proposed `compat` relaxation (entry words: the annotation's
# may be a prefix of the incoming ones). Off by default: the committed
# checker requires equal lengths.
ARGS_PREFIX = False
# Prototype of the proposed per-entry summaries: a goto needs the target's
# summary to be covered by the jumper's (`retLe`), not equal. Off by default.
SUB_SUMMARY = False


def known(t) -> bool:
    """Term.known: the term mentions no `top`."""
    k = t[0]
    if k == 'top':
        return False
    if k == 'cd':
        return known(t[1])
    if k == 'op2':
        return known(t[2]) and known(t[3])
    if k == 'kecc':
        return known(t[1]) and known(t[2])
    if k == 'kecc1':
        return known(t[1])
    return True


def mk_cd(t):
    return ('cd', t) if known(t) else TOP


def mk_kecc(a, b):
    return ('kecc', a, b) if known(a) and known(b) else TOP


def mk_kecc1(t):
    return ('kecc1', t) if known(t) else TOP


def mk_op2_prime(o, a, b):
    """mkOp2': `AND` with the mask it already carries is the same word."""
    if o == 'and' and a[0] == 'op2' and a[1] == 'and' and a[3][0] == 'const' \
            and b[0] == 'const' and a[3][1] == b[1]:
        return a
    return ('op2', o, a, b)


def mk_op2(o, a, b):
    """mkOp2: constants fold, `top` absorbs, a commutative constant goes right."""
    if known(a) and known(b):
        if a[0] == 'const' and b[0] == 'const':
            return ('const', OP2_EVAL[o](a[1], b[1]))
        if a[0] == 'const' and b[0] != 'const':
            if o in OP2_COMM:
                return mk_op2_prime(o, b, a)
            return ('op2', o, a, b)
        return mk_op2_prime(o, a, b)
    return TOP


def term_subst(t, pa):
    """Term.subst: `arg i` becomes the caller's term for the callee's entry
    word; smart constructors re-collapse (folding or `top`)."""
    k = t[0]
    if k == 'arg':
        i = t[1]
        return pa[i] if 0 <= i < len(pa) else TOP
    if k == 'cd':
        return mk_cd(term_subst(t[1], pa))
    if k == 'op2':
        return mk_op2(t[1], term_subst(t[2], pa), term_subst(t[3], pa))
    if k == 'kecc':
        return mk_kecc(term_subst(t[1], pa), term_subst(t[2], pa))
    if k == 'kecc1':
        return mk_kecc1(term_subst(t[1], pa))
    return t


def show_term(t) -> str:
    k = t[0]
    if k == 'const':
        return f"0x{t[1]:x}"
    if k == 'arg':
        return f"arg{t[1]}"
    if k == 'cd':
        return f"cd({show_term(t[1])})"
    if k == 'op2':
        return f"({t[1]} {show_term(t[2])} {show_term(t[3])})"
    if k == 'kecc':
        return f"kecc({show_term(t[1])},{show_term(t[2])})"
    if k == 'kecc1':
        return f"kecc1({show_term(t[1])})"
    return k  # top, caller, self


class WSt:
    """Abstract frame state. Mirrors WriteSite.WSt: `kv` (top first), `args`
    (entry words), `facts` (FreePtr facts, set semantics), `prov`/`mem`/
    `cur`/`ub`/`eqs`/`guards` as ordered first-match lists (Lean `lookup`
    reads the first entry, so duplicates are never created and `canon`
    drops them keeping the first)."""

    __slots__ = ('kv', 'args', 'facts', 'prov', 'mem', 'cur', 'ub',
                 'eqs', 'guards')

    def __init__(self, kv, args, facts, prov, mem, cur, ub, eqs, guards):
        self.kv = tuple(kv)
        self.args = tuple(args)
        self.facts = frozenset(facts)
        self.prov = tuple(prov)
        self.mem = tuple(mem)
        self.cur = tuple(cur)
        self.ub = tuple(ub)
        self.eqs = tuple(eqs)
        self.guards = tuple(guards)

    def key(self):
        return (self.kv, self.args, self.facts, self.prov, self.mem,
                self.cur, self.ub, self.eqs, self.guards)

    def __eq__(self, o):
        return isinstance(o, WSt) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())


def wst_param(n: int) -> WSt:
    """WSt.param: the state a callee is entered in (symbols 1..n)."""
    ks = tuple(range(1, n + 1))
    return WSt(ks, ks, frozenset(),
               tuple((i + 1, ('arg', i)) for i in range(n)),
               (), (), (), (), ())


INIT = wst_param(0)  # WSt.init


class WRet:
    """A function's summary: returned words' terms (top first), order facts,
    whether it keeps storage, and the write sites of it and its callees."""

    __slots__ = ('prov', 'les', 'keeps', 'sites')

    def __init__(self, prov, les, keeps, sites):
        self.prov = tuple(prov)
        self.les = frozenset(les)
        self.keeps = keeps
        self.sites = frozenset(sites)

    def key(self):
        return (self.prov, self.les, self.keeps, self.sites)

    def __eq__(self, o):
        return isinstance(o, WRet) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())


def prov_of(st: WSt, s):
    """WSt.provOf (first match; absent: `top`)."""
    for k, t in st.prov:
        if k == s:
            return t
    return TOP


def mem_lookup(st: WSt, o):
    for k, s in st.mem:
        if k == o:
            return s
    return None


def cur_find(st: WSt, t):
    """sloadName's lookup: the symbol of the current value at slot term."""
    for s, u in st.cur:
        if u == t:
            return s
    return None


def const_of_w(st: WSt, s) -> Optional[int]:
    """WSt.constOf: provenance-based (NOT fact-based)."""
    t = prov_of(st, s)
    return t[1] if t[0] == 'const' else None


def fresh_w(st: WSt) -> int:
    """WSt.fresh: one above every symbol the state mentions."""
    m = 0
    for s in st.kv:
        m = max(m, s)
    for s in st.args:
        m = max(m, s)
    for f in st.facts:
        for s in fact_syms(f):
            m = max(m, s)
    for k, _ in st.prov:
        m = max(m, k)
    for _, s in st.mem:
        m = max(m, s)
    for k, _ in st.cur:
        m = max(m, k)
    for k, _ in st.ub:
        m = max(m, k)
    for k, _, _ in st.eqs:
        m = max(m, k)
    return m + 1


def live_syms(st: WSt):
    """WSt.liveSyms."""
    return list(st.kv) + list(st.args) + [s for _, s in st.mem] + \
        [s for s, _ in st.cur] + [s for s, _ in st.ub]


def close_live_w(fs, alive_list):
    """One round of WriteSite.closeLive: the operands of a comparison fact
    whose result is kept stay."""
    alive = list(alive_list)
    out = list(alive)
    for f in fs:
        k = f[0]
        if k == 'isz' and f[1] in alive:
            out.append(f[2])
        elif k == 'ltr' and f[1] in alive:
            out.extend((f[2], f[3]))
        elif k == 'orr' and f[1] in alive:
            out.extend((f[2], f[3]))
    return out


def prune(st: WSt) -> WSt:
    """WSt.prune: drop what speaks of dead symbols (comparison chains closed
    twice; `cur`/`ub`/`mem`/`guards` are never pruned)."""
    from symcore import syms as fact_syms
    live = set(close_live_w(st.facts, close_live_w(st.facts, live_syms(st))))
    facts = frozenset(f for f in st.facts
                      if all(s in live for s in fact_syms(f)))
    prov = tuple(p for p in st.prov if p[0] in live)
    eqs = tuple(e for e in st.eqs if e[0] in live)
    return WSt(st.kv, st.args, facts, prov, st.mem, st.cur, st.ub, eqs,
               st.guards)


def mem_kill_s(m, lo, hi):
    """memKillS: forget the memory words overlapping `[lo, hi)`."""
    return tuple(p for p in m if p[0] + 32 <= lo or hi <= p[0])


def mem_below(m, b):
    """memBelow: keep only the memory words ending at or below `b`."""
    return tuple(p for p in m if p[0] + 32 <= b)


# rinstMemKeeps (CheckMem.lean) over ninst_kind names; pushes and dup/swap
# keep the map, every exec instruction forgets it.
MEM_KEEPS = {
    'add', 'mul', 'sub', 'div', 'sdiv', 'mod', 'smod', 'signextend',
    'lt', 'gt', 'slt', 'sgt', 'eq', 'and', 'or', 'xor', 'byte', 'shl',
    'shr', 'sar', 'iszero', 'not', 'address', 'origin', 'caller',
    'callvalue', 'calldatasize', 'codesize', 'gasprice', 'returndatasize',
    'coinbase', 'timestamp', 'number', 'prevrandao', 'gaslimit', 'chainid',
    'basefee', 'blobbasefee', 'msize', 'pop', 'calldataload', 'mload',
    'keccak256', 'dup', 'swap', 'sload', 'sstore', 'tload', 'tstore', 'log',
}


def mem_keeps(kind) -> bool:
    """ninstMemKeeps: every PUSH, and the keeping regular instructions."""
    if kind[0] in ('push', 'dup', 'swap'):
        return True
    if kind[0] == 'reg':
        return kind[1] in MEM_KEEPS
    return False


def mem_eff_w(st: WSt, kind, xs) -> tuple:
    """The memory effect of `n` over its input symbols (WriteSite.memEff)."""
    lo = lambda s: bnd2(st.facts, s)[0]  # noqa: E731 FreePtr.lo
    if kind == ('reg', 'mstore') and len(xs) >= 2:
        a, v = xs[0], xs[1]
        o = const_of_w(st, a)
        if o is not None:
            return ((o, v),) + mem_kill_s(st.mem, o, o + 32)
        return mem_below(st.mem, lo(a))
    if kind == ('reg', 'mstore8') and len(xs) >= 2:
        a = xs[0]
        o = const_of_w(st, a)
        if o is not None:
            return mem_kill_s(st.mem, o, o + 1)
        return mem_below(st.mem, lo(a))
    if kind == ('reg', 'calldatacopy') and len(xs) >= 3:
        return mem_below(st.mem, lo(xs[0]))
    if kind == ('reg', 'codecopy') and len(xs) >= 3:
        return mem_below(st.mem, lo(xs[0]))
    if kind == ('reg', 'returndatacopy') and len(xs) >= 3:
        return mem_below(st.mem, lo(xs[0]))
    if kind == ('reg', 'mcopy') and len(xs) >= 3:
        return mem_below(st.mem, lo(xs[0]))
    if kind == ('reg', 'extcodecopy') and len(xs) >= 4:
        return mem_below(st.mem, lo(xs[1]))
    if kind in (('exec', 'call'), ('exec', 'callcode')) and len(xs) >= 7:
        return mem_below(st.mem, lo(xs[5]))
    if kind in (('exec', 'delegatecall'), ('exec', 'staticcall')) \
            and len(xs) >= 6:
        return mem_below(st.mem, lo(xs[4]))
    if mem_keeps(kind):
        return st.mem
    return ()


def prov_eff_w(st: WSt, kind, xs):
    """The term of the fresh result of `n` (WriteSite.provEff)."""
    if kind == ('reg', 'caller'):
        return ('caller',)
    if kind == ('reg', 'address'):
        return ('self',)
    if kind == ('reg', 'calldataload') and len(xs) >= 1:
        return mk_cd(prov_of(st, xs[0]))
    if kind == ('reg', 'not') and len(xs) >= 1:
        t = prov_of(st, xs[0])
        return ('const', (MAXW - t[1]) % M) if t[0] == 'const' else TOP
    if kind == ('reg', 'keccak256') and len(xs) >= 2:
        o, ln = const_of_w(st, xs[0]), const_of_w(st, xs[1])
        if o is not None and ln == 64:
            s0, s1 = mem_lookup(st, o), mem_lookup(st, o + 32)
            if s0 is not None and s1 is not None:
                return mk_kecc(prov_of(st, s0), prov_of(st, s1))
            return TOP
        if o is not None and ln == 32:
            s0 = mem_lookup(st, o)
            return mk_kecc1(prov_of(st, s0)) if s0 is not None else TOP
        return TOP
    if kind[0] == 'reg' and len(xs) >= 2 and kind[1] in OP2_REG:
        return mk_op2(kind[1], prov_of(st, xs[0]), prov_of(st, xs[1]))
    return TOP


def sload_name(st: WSt, kind, xs):
    """sloadName: the symbol of the current value at an SLOAD's slot."""
    if kind == ('reg', 'sload') and len(xs) >= 1:
        t = prov_of(st, xs[0])
        if known(t):
            return cur_find(st, t)
    return None


def site_of(st: WSt, k, v):
    """The observed site of an `SSTORE(k, v)`."""
    t = prov_of(st, k)
    non_inc = known(t) and (
        (v, t) in st.ub or (v, t) in st.cur or
        any(p[1] == t and entails(st.facts, ('le', v, p[0]))
            for p in st.cur))
    return (t, tuple(st.guards), non_inc)


def site_covers(s, o) -> bool:
    """Site.covers: the listed site covers the observed site."""
    return (s[0] == TOP or s[0] == o[0]) and \
        all(g in o[1] for g in s[1]) and (not s[2] or o[2])


def writes_stor(kind) -> bool:
    """Ninst.writesStor: SSTORE, or any call but STATICCALL."""
    return kind == ('reg', 'sstore') or \
        (kind[0] == 'exec' and kind != ('exec', 'staticcall'))


def wstep(R: WRet, op: int, data: bytes, kind, lab, st: WSt,
          pc: int) -> WSt:
    """One non-jump instruction on the abstract state under `R`
    (WriteSite.wstep); Reject on an uncovered SSTORE, a storage write in a
    keeping function, or a transfer-shape failure."""
    if kind[0] == 'push':
        r = fresh_w(st)
        c = int.from_bytes(data, 'big')  # Bytes.toB256, big-endian
        return prune(WSt((r,) + st.kv, st.args,
                         st.facts | frozenset({('bnd', r, c, c)}),
                         ((r, ('const', c)),) + st.prov,
                         st.mem, st.cur, st.ub, st.eqs, st.guards))
    if lab is None:
        raise Reject(f"stack underflow at {pc:#x}")
    if lab.count(None) > 1:
        raise Reject(f"two fresh words at {pc:#x}")
    if R.keeps and writes_stor(kind):
        raise Reject(f"storage write at {pc:#x} in a keeping function")
    xs = list(st.kv)
    if kind == ('reg', 'sstore'):
        if len(xs) < 2:
            raise Reject(f"SSTORE at {pc:#x}: stack underflow")
        obs = site_of(st, xs[0], xs[1])
        if not any(site_covers(s, obs) for s in R.sites):
            raise Reject(f"SSTORE at {pc:#x}: no listed site covers "
                         f"{show_term(obs[0])}")
    r = fresh_w(st)
    hit = sload_name(st, kind, xs)
    r2 = hit if hit is not None else r
    kv2 = []
    for l in lab:
        if l is None:
            kv2.append(r2)
        else:
            if l >= len(st.kv):
                raise Reject(f"transfer label {l} out of range at {pc:#x}")
            kv2.append(st.kv[l])
    t = prov_eff_w(st, kind, xs)
    # a symbolic `SUB` below its minuend
    sub_le: Set[Tuple] = set()
    sub_ub: List[Tuple] = []
    if kind == ('reg', 'sub') and len(xs) >= 2:
        x, y = xs[0], xs[1]
        if entails(st.facts, ('le', y, x)):
            sub_le = {('le', r, x)}
            sub_ub = [(r, tt) for (ss, tt) in
                      list(st.cur) + list(st.ub) if ss == x]
    new_cur: List[Tuple] = []
    if kind == ('reg', 'sload') and len(xs) >= 1:
        tt = prov_of(st, xs[0])
        if known(tt) and r2 == r:
            new_cur = [(r, tt)]
    keep_stor = not writes_stor(kind)
    eqs_new: List[Tuple] = []
    if kind == ('reg', 'eq') and len(xs) >= 2:
        eqs_new = [(r, prov_of(st, xs[0]), prov_of(st, xs[1]))]
    return prune(WSt(
        kv2, st.args,
        frozenset(sub_le) | op_facts(st.facts, kind, xs, r) | st.facts,
        (((r, t),) if known(t) and r2 == r else ()) + st.prov,
        mem_eff_w(st, kind, xs),
        tuple(new_cur) + (st.cur if keep_stor else ()),
        tuple(sub_ub) + (st.ub if keep_stor else ()),
        tuple(eqs_new) + st.eqs,
        st.guards))


def eq_guard(t, u):
    """eqGuard: the guard a nonzero `EQ` result over terms gives."""
    if u[0] == 'const' and known(t):
        return (t, u[1])
    if t[0] == 'const' and known(u):
        return (u, t[1])
    return None


def refine_w(st: WSt, c: int, kv, zero: bool) -> WSt:
    """WriteSite.refine: a JUMPI on condition symbol `c`."""
    g = [] if zero else \
        [gg for e in st.eqs if e[0] == c
         for gg in [eq_guard(e[1], e[2])] if gg is not None]
    return prune(WSt(kv, st.args, refine_facts(st.facts, c, zero), st.prov,
                     st.mem, st.cur, st.ub, st.eqs,
                     tuple(g) + st.guards))


def popped_w(st: WSt, kv) -> WSt:
    return prune(WSt(kv, st.args, st.facts, st.prov, st.mem, st.cur, st.ub,
                     st.eqs, st.guards))


def _build_map(A: WSt, st: WSt):
    m = {}
    for x, s in zip(list(A.kv) + list(A.args), list(st.kv) + list(st.args)):
        if x not in m:
            m[x] = s
    return m


def sym_map_w(A: WSt, st: WSt, a: int) -> int:
    """symMap: the incoming symbol an annotation symbol names."""
    return _build_map(A, st).get(a, 0)


def compat_w(st: WSt, A: WSt) -> Optional[str]:
    """The incoming state satisfies the annotation (WriteSite.compat)."""
    if len(st.kv) != len(A.kv):
        return "length"
    if (len(A.args) > len(st.args)) if ARGS_PREFIX else (len(st.args) != len(A.args)):
        return "args length"
    m = _build_map(A, st)
    for x, s in zip(list(A.kv) + list(A.args), list(st.kv) + list(st.args)):
        if m[x] != s:
            return "partition"
    own = list(A.kv) + list(A.args)
    syms_a = list(A.kv) + list(A.args)
    for f in A.facts:
        syms_a.extend(fact_syms(f))
    syms_a.extend(k for k, _ in A.prov)
    syms_a.extend(s for _, s in A.mem)
    syms_a.extend(s for s, _ in A.cur)
    syms_a.extend(s for s, _ in A.ub)
    syms_a.extend(e[0] for e in A.eqs)
    if not all(s in own for s in syms_a):
        return "annotation names a symbol outside its frame"
    for f in A.facts:
        if not entails(st.facts, _rename_fact(f, m)):
            return f"fact {f}"
    for k, t in A.prov:
        if known(t) and prov_of(st, m.get(k, 0)) != t:
            return f"prov {k}"
    for o, s in A.mem:
        if (o, m.get(s, 0)) not in st.mem:
            return f"mem {o}"
    for s, t in A.cur:
        if (m.get(s, 0), t) not in st.cur:
            return f"cur {(s, t)}"
    for s, t in A.ub:
        if (m.get(s, 0), t) not in st.ub and \
                (m.get(s, 0), t) not in st.cur:
            return f"ub {(s, t)}"
    for e in A.eqs:
        if (m.get(e[0], 0), e[1], e[2]) not in st.eqs:
            return f"eq {e}"
    for g in A.guards:
        if g not in st.guards:
            return f"guard {g}"
    return None


def _rename_fact(f, m):
    return srename(f, lambda s: m.get(s, 0))


def _canon_site(obs):
    """Canonical site form: guards sorted, so equal observations are one
    listed site regardless of the path that produced them."""
    t, guards, non_inc = obs
    return (t, tuple(sorted(guards, key=lambda g: (show_term(g[0]), g[1]))),
            non_inc)


def inst_site(pa, gs, s):
    """instSite: a callee site instantiated at a call."""
    slot = term_subst(s[0], pa)
    guards = tuple(gg for g in s[1]
                   for gg in [(term_subst(g[0], pa), g[1])]
                   if known(gg[0])) + tuple(gs)
    return (slot, guards, s[2])


def resume_w(st: WSt, cw, below, R: WRet, rets: int) -> WSt:
    """The state a call continuation resumes in (WriteSite.resume)."""
    base = fresh_w(st)
    pa = [prov_of(st, s) for s in cw]
    rs = [base + j for j in range(rets)]
    prov = tuple((base + j, term_subst(R.prov[j], pa))
                 for j in range(len(R.prov))
                 if known(term_subst(R.prov[j], pa)))
    les = frozenset(('le', base + p[0], s)
                    for p in R.les if p[1] < len(cw)
                    for s in [cw[p[1]]])
    ubs = []
    if R.keeps:
        for p in R.les:
            if p[1] < len(cw):
                s = cw[p[1]]
                ubs.extend((base + p[0], t) for (ss, t) in
                           list(st.cur) + list(st.ub) if ss == s)
    return prune(WSt(
        tuple(rs) + tuple(below), st.args,
        les | st.facts,
        prov + st.prov,
        (),
        st.cur if R.keeps else (),
        tuple(ubs) + (st.ub if R.keeps else ()),
        st.eqs, st.guards))


def ret_ok(st: WSt, kv, R: WRet) -> Optional[str]:
    """retOk: the returned words meet the summary."""
    if len(kv) != len(R.prov):
        return "length"
    for t, s in zip(R.prov, kv):
        if known(t) and prov_of(st, s) != t:
            return f"prov {show_term(t)}"
    for p in R.les:
        if p[0] >= len(kv) or p[1] >= len(st.args):
            return f"order {p}"
        if not entails(st.facts, ('le', kv[p[0]], st.args[p[1]])):
            return f"order {p}"
    return None


def _dedupe_first(xs):
    seen, out = set(), []
    for x in xs:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return tuple(out)


def resolve_args(entries, trees, called):
    """Entry-word assignment forced by the goto graph: every jump/branchTo
    edge S->T needs `len(args[S]) == len(args[T])` (WriteSite.compat), and
    called entries plus entry 0 are pinned (`WSt.param`, `WSt.init`). A
    union-find set with two different pins is a structural conflict: no
    single annotation satisfies all its jumps (reported, first pin wins so
    the producer stays total). Unpinned sets (unreachable from every pin)
    take `()`."""
    n = len(entries)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    # Only jump/branchTo edges constrain entry words (no compat is checked
    # at calls or joins in Lean's wsNode).
    edges = []
    for k, t in trees.items():
        stack = [t]
        while stack:
            u = stack.pop()
            kind = u['kind']
            if kind in ('jump', 'branchTo'):
                tgt = u['target_entry']
                if 0 <= tgt < n:
                    edges.append((k, tgt))
            if kind == 'next':
                stack.append(u['sub'])
            elif kind == 'dest':
                stack.append(u['sub'])
            elif kind == 'branch':
                stack.append(u['fall'])
                stack.append(u['taken'])
            elif kind == 'branchTo':
                stack.append(u['fall'])
            elif kind == 'callNext':
                stack.append(u['continuation'])
            elif kind == 'join':
                if u['target_entry'] in trees:
                    stack.append(trees[u['target_entry']])
    for a, b in edges:
        union(a, b)
    pins: Dict[int, tuple] = {0: ()}
    for ck in called:
        pins[ck] = tuple(range(1, len(entries[ck][1]) + 1))
    argmap: Dict[int, tuple] = {}
    conflicts = []
    if ARGS_PREFIX:
        # each goto S->T needs len(args[T]) <= len(args[S]); unpinned entries
        # take the least length over their sources (fixpoint, lengths only fall)
        length: Dict[int, int] = dict((k, len(v)) for k, v in pins.items())
        changed = True
        while changed:
            changed = False
            for a, b in edges:
                if a in length and b not in pins:
                    if b not in length or length[a] < length[b]:
                        length[b] = length[a]
                        changed = True
        for a, b in edges:
            if b in pins and a in length and length[a] < length[b]:
                conflicts.append((b, [a, b], [length[a], length[b]]))
        argmap = {k: tuple(range(1, length.get(k, 0) + 1)) for k in range(n)}
        return argmap, conflicts, edges
    by_root: Dict[int, List[int]] = {}
    for k in range(n):
        by_root.setdefault(find(k), []).append(k)
    for r, members in by_root.items():
        seen = []
        for m in members:
            if m in pins and pins[m] not in seen:
                seen.append(pins[m])
        if len(seen) > 1:
            conflicts.append((r, sorted(members), seen))
        argmap.update({m: (seen[0] if seen else ()) for m in members})
    return argmap, conflicts, edges


class Checker:
    """Fixpoint inference plus self-check for write-site annotations."""

    def __init__(self, entries, trees, effects, lean_reg, step_inst):
        self.entries = entries
        self.trees = trees
        self.effects = effects
        self.lean_reg = lean_reg
        self.step_inst = step_inst
        self.ann: Dict[int, WSt] = {}
        self.ret_prov: Dict[int, tuple] = {}
        self.ret_les: Dict[int, FrozenSet] = {}
        self.sites: Dict[int, Set] = {}
        self.incoming: Dict[int, List[WSt]] = {}
        self.retobs: Dict = {}
        self.flows: Dict[int, List[WSt]] = {}
        self.incoming_src: Dict[int, List[int]] = {}
        self.seeded: Dict[int, str] = {}
        self.stores: List = []
        self.cost: Dict[int, int] = {}
        self.notes: List[str] = []
        self.mode = 'infer'
        self._noted = set()
        self.called = self._called_entries()
        self.argmap, self.conflicts, self.edges = resolve_args(
            entries, trees, self.called)
        self.comp = components(len(entries), trees)
        self.comp_n = {c: comp_rets(self.entries, self.comp, c)
                       for c in set(self.comp.values())}
        self.keeps = self._compute_keeps()
        self._sites_grew = False

    def _called_entries(self) -> Set[int]:
        out = set()
        for t in self.trees.values():
            stack = [t]
            while stack:
                u = stack.pop()
                kind = u['kind']
                if kind == 'callNext' and 0 <= u['target_entry'] < len(self.entries):
                    out.add(u['target_entry'])
                if kind == 'next':
                    stack.append(u['sub'])
                elif kind == 'dest':
                    stack.append(u['sub'])
                elif kind == 'branch':
                    stack.append(u['fall'])
                    stack.append(u['taken'])
                elif kind == 'branchTo':
                    stack.append(u['fall'])
                elif kind == 'callNext':
                    stack.append(u['continuation'])
        return out

    def _compute_keeps(self) -> Dict[int, bool]:
        """keeps per component: no SSTORE, no call but STATICCALL in its
        trees, and only keeping callees. The wsNode walk covers every
        statically present instruction (both branch arms), so the scan is
        exact; the `!R.keeps || A.ret.keeps` gate becomes the callee fixpoint."""
        writes = set()
        call_edges: Dict[int, Set[int]] = {}
        for k, t in self.trees.items():
            stack, seen = [t], set()
            while stack:
                u = stack.pop()
                if id(u) in seen:
                    continue
                seen.add(id(u))
                kind = u['kind']
                if kind == 'next':
                    op = int(u['op'], 16)
                    try:
                        kk = ninst_kind(op, self.lean_reg)
                    except Reject:
                        kk = ('exec', 'unknown')
                    if writes_stor(kk):
                        writes.add(self.rkey(k))
                    stack.append(u['sub'])
                elif kind == 'dest':
                    stack.append(u['sub'])
                elif kind == 'branch':
                    stack.append(u['fall'])
                    stack.append(u['taken'])
                elif kind == 'branchTo':
                    stack.append(u['fall'])
                    if SUB_SUMMARY and 0 <= u['target_entry'] < len(self.entries):
                        call_edges.setdefault(k, set()).add(u['target_entry'])
                elif kind == 'jump':
                    if SUB_SUMMARY and 0 <= u['target_entry'] < len(self.entries):
                        call_edges.setdefault(k, set()).add(u['target_entry'])
                elif kind == 'callNext':
                    ck = u['target_entry']
                    if 0 <= ck < len(self.entries):
                        call_edges.setdefault(self.rkey(k), set()).add(self.rkey(ck))
                    stack.append(u['continuation'])
                elif kind == 'join':
                    if u['target_entry'] in self.trees:
                        stack.append(self.trees[u['target_entry']])
        keys = range(len(self.entries)) if SUB_SUMMARY else set(self.comp.values())
        keeps = {c: (c not in writes) for c in keys}
        changed = True
        while changed:
            changed = False
            for c, ds in call_edges.items():
                if keeps.get(c, True) and any(not keeps.get(d, True) for d in ds):
                    keeps[c] = False
                    changed = True
        return keeps

    def comp_rets(self, c: int) -> int:
        return comp_rets(self.entries, self.comp, c)

    # -- canonical annotations and their join
    @staticmethod
    def canon(st: WSt) -> WSt:
        ren: Dict[int, int] = {}
        for s in st.kv:
            if s not in ren:
                ren[s] = len(ren)
        kv = tuple(ren[s] for s in st.kv)
        # Entry-word symbols take negative canonical indices: they never
        # collide with the frame renumbering (whose values are 0, 1, ...),
        # and every canon of one function names them the same way, so the
        # join's entry-word equality still holds.
        argidx: Dict[int, int] = {}
        for s in st.args:
            if s not in argidx:
                argidx[s] = -(len(argidx) + 1)
        cargs = tuple(argidx[s] for s in st.args)
        keep = lambda s: ren[s] if s in ren else argidx[s] if s in argidx else s  # noqa: E731
        known_sym = lambda s: s in ren or s in argidx  # noqa: E731
        facts = set()
        for f in st.facts:
            if f[0] in ('bnd', 'rds'):
                continue
            if all(known_sym(s) for s in fact_syms(f)):
                facts.add(srename(f, keep))
        spots = set(kv) | set(cargs)
        for s in spots:
            orig = next((o for o in list(st.kv) + list(st.args)
                         if keep(o) == s), None)
            if orig is None:
                continue
            lo, hi = sbnd2(st.facts, orig)
            if (lo, hi) != (0, MAXW):
                facts.add(('bnd', s, lo, hi))
        return WSt(
            kv, cargs, frozenset(facts),
            _dedupe_first((keep(k), t) for k, t in st.prov
                           if known_sym(k) and known(t)),
            _dedupe_first((o, keep(s)) for o, s in st.mem
                           if known_sym(s)),
            _dedupe_first((keep(s), t) for s, t in st.cur
                           if known_sym(s)),
            _dedupe_first((keep(s), t) for s, t in st.ub
                           if known_sym(s)),
            _dedupe_first((keep(r), t, u) for r, t, u in st.eqs
                           if known_sym(r)),
            tuple(st.guards))

    def join(self, a: Optional[WSt], b: WSt, k, widen: Dict) -> WSt:
        if a is None:
            return b
        if len(a.kv) != len(b.kv):
            raise Reject(f"entry {k}: incoming frames of different lengths")
        if ARGS_PREFIX:
            n_args = 0
            while (n_args < min(len(a.args), len(b.args))
                   and a.args[n_args] == b.args[n_args]):
                n_args += 1
            a = WSt(a.kv, a.args[:n_args], a.facts, a.prov, a.mem, a.cur,
                    a.ub, a.eqs, a.guards)
            b = WSt(b.kv, b.args[:n_args], b.facts, b.prov, b.mem, b.cur,
                    b.ub, b.eqs, b.guards)
        if tuple(a.args) != tuple(b.args):
            raise Reject(f"entry {k}: incoming entry words differ")
        first: Dict[Tuple[int, int], int] = {}
        kv = []
        for j, pair in enumerate(zip(a.kv, b.kv)):
            if pair not in first:
                first[pair] = j
            kv.append(first[pair])
        kv = tuple(kv)
        ma: Dict[int, int] = {}
        mb: Dict[int, int] = {}
        for j, s in enumerate(kv):
            if a.kv[j] not in ma:
                ma[a.kv[j]] = s
            if b.kv[j] not in mb:
                mb[b.kv[j]] = s
        ra = lambda s: ma.get(s, s)  # noqa: E731
        rb = lambda s: mb.get(s, s)  # noqa: E731
        fa = {srename(f, ra) for f in a.facts
              if all(x in ma or x in a.args for x in fact_syms(f))}
        fb = {srename(f, rb) for f in b.facts
              if all(x in mb or x in b.args for x in fact_syms(f))}
        facts = {f for f in fa & fb if f[0] != 'bnd'}
        spots = set(kv) | set(a.args)
        for s in spots:
            la, ha = sbnd_of(fa, s)
            lb, hb = sbnd_of(fb, s)
            lo, hi = min(la, lb), max(ha, hb)
            if widen.get(k, 0) > WIDEN_AFTER and (lo, hi) != (la, ha):
                lo, hi = widen_hull(lo, hi, la, ha)
            if (lo, hi) != (0, MAXW):
                facts.add(('bnd', s, lo, hi))

        def inter(pa_list, pb_list):
            sb = set(pb_list)
            return _dedupe_first(x for x in pa_list if x in sb)

        return WSt(
            kv, tuple(a.args), frozenset(facts),
            inter(tuple((ra(k2), t) for k2, t in a.prov),
                  tuple((rb(k2), t) for k2, t in b.prov)),
            inter(tuple((o, ra(s)) for o, s in a.mem),
                  tuple((o, rb(s)) for o, s in b.mem)),
            inter(tuple((ra(s), t) for s, t in a.cur),
                  tuple((rb(s), t) for s, t in b.cur)),
            inter(tuple((ra(s), t) for s, t in a.ub),
                  tuple((rb(s), t) for s, t in b.ub)),
            inter(tuple((ra(r), t, u) for r, t, u in a.eqs),
                  tuple((rb(r), t, u) for r, t, u in b.eqs)),
            inter(a.guards, b.guards))

    # -- single steps
    def astep(self, pc: int, op: int, data: bytes, a: List[Tuple]) -> List[Tuple]:
        """Mirror of absNinst: lift's own abstract transfer (with the row's
        fold setting), which the pipeline's self-check already validates."""
        out = self.step_inst(op, data, list(a), None)
        if out is None:
            raise Reject(f"abstract transfer fails for {op:#x} at {pc:#x}")
        return [tuple(v) for v in out]

    def default_ret(self, c: int) -> WRet:
        n = self.comp_n[c]
        return WRet([TOP] * n, frozenset(), self.keeps.get(c, True),
                    self.sites.get(c, frozenset()))

    def get_ret(self, c: int) -> WRet:
        """The stored return summary, else the default (only stored summaries
        drive callers; sites accumulate live in `self.sites`)."""
        n = self.comp_n[c]
        prov = self.ret_prov.get(c, tuple([TOP] * n))
        return WRet(prov, self.ret_les.get(c, frozenset()),
                    self.keeps.get(c, True),
                    self.sites.get(c, frozenset()))

    def rkey(self, k: int) -> int:
        """The key of entry k's sites and keeps: its component, or (under the
        per-entry prototype) the entry itself."""
        return k if SUB_SUMMARY else self.comp[k]

    def get_ret_e(self, k: int) -> WRet:
        """Entry k's summary: the component's return words and order facts,
        the key's keeps and sites."""
        c = self.comp[k]
        r = self.rkey(k)
        n = self.comp_n[c]
        return WRet(self.ret_prov.get(c, tuple([TOP] * n)),
                    self.ret_les.get(c, frozenset()),
                    self.keeps.get(r, True), self.sites.get(r, frozenset()))

    def _cover(self, c: int, obs) -> None:
        """Infer mode: list the observed site when nothing covers it yet."""
        if not any(site_covers(s, obs) for s in self.sites.get(c, frozenset())):
            self.sites.setdefault(c, set()).add(_canon_site(obs))
            self._sites_grew = True

    def goto(self, k: int, st: WSt, what: str, cur: int, is_join: bool = False,
             check_ret: bool = True, do_compat: bool = True):
        if k < 0 or k >= len(self.entries):
            raise Reject(f"{what} to entry {k}: out of range")
        if self.mode == 'infer':
            if is_join:
                # Fallthrough joins carry no compat obligation in Lean; their
                # states only seed join-only targets that no goto reaches.
                self.flows.setdefault(k, []).append(st)
            else:
                self.incoming.setdefault(k, []).append(st)
                self.incoming_src.setdefault(k, []).append(cur)
                if SUB_SUMMARY and check_ret:
                    for s in sorted(self.sites.get(self.rkey(k), ()), key=repr):
                        self._cover(self.rkey(cur), s)
            return
        if is_join or not do_compat:
            # Lean's wsNode checks no compat at a call (only the parameter
            # state equality, enforced in walk) and none at a join.
            return
        A = self.ann.get(k)
        if A is None:
            raise Reject(f"{what} to entry {k}: no annotation")
        why = compat_w(st, A)
        if why is not None and ARGS_PREFIX and self._tail_ok(k, st, cur):
            why = None
        if why is not None:
            raise Reject(f"{what} to entry {k} "
                         f"(pc {self.entries[k][0]:#x}): {why}")
        if check_ret and not self._ret_ok_goto(k, cur):
            raise Reject(f"{what} to entry {k}: return summary differs")

    def _ret_ok_goto(self, k: int, cur: int) -> bool:
        """The goto's summary condition: equality, or under the prototype the
        target's summary below the jumper's (`retLe`)."""
        Rt, Rs = self.get_ret_e(k), self.get_ret_e(cur)
        if not SUB_SUMMARY:
            return Rt == Rs
        return (tuple(Rt.prov) == tuple(Rs.prov) and Rt.les == Rs.les
                and (not Rs.keeps or Rt.keeps)
                and all(any(site_covers(q, s) for q in Rs.sites) for s in Rt.sites))

    def _tail_ok(self, k: int, st: WSt, cur: int) -> bool:
        """Prototype of the proposed tail-call goto: a jump into a callee
        entry (parameter annotation) whose shared summary names no entry
        word, with the callee's frame on the stack."""
        n = len(self.entries[k][1])
        # the target's summary is read in the callee environment: it must
        # name no entry word (under SUB_SUMMARY the target's own summary,
        # else the shared one)
        R = self.get_ret_e(k if SUB_SUMMARY else cur)
        return (self.ann.get(k) == wst_param(n) and len(st.kv) >= n
                and ret_arg_free(R))

    def walk(self, t, a: List[Tuple], st: WSt, R: WRet, k: int):
        """Walk tree `t` (json) from AVal stack `a` and state `st`, under the
        current function's summary `R`. Mirrors WriteSite.wsNode."""
        kind = t['kind']
        if kind == 'join':
            j = t['target_entry']
            self.goto(j, st, f"join at {t.get('pc', -1):#x}", k, is_join=True)
            self.walk(self.trees[j], a, st, R, k)
            return
        if kind == 'next':
            pc = t['pc']
            op = int(t['op'], 16)
            data = bytes.fromhex(t['data'])
            a2 = self.astep(pc, op, data, a)
            kk = ninst_kind(op, self.lean_reg)
            if self.mode == 'infer':
                # List the observed site first: wstep below checks coverage
                # against the summary, which must already include it.
                if kk == ('reg', 'sstore') and len(st.kv) >= 2:
                    self._cover(self.rkey(k), site_of(st, st.kv[0], st.kv[1]))
                R = self.get_ret_e(k)
            lab = None if kk[0] == 'push' else lockann.labels(op, len(st.kv), self.effects)
            st2 = wstep(R, op, data, kk, lab, st, pc)
            if self.mode == 'check':
                # cost proxy for the kernel decide of entry k (Check part balance)
                self.cost[k] = self.cost.get(k, 0) + 1 + len(st.facts) + len(st.prov)
            if self.mode == 'check' and kk == ('reg', 'sstore'):
                obs = site_of(st, st.kv[0], st.kv[1])
                self.stores.append((k, pc, obs))
            self.walk(t['sub'], a2, st2, R, k)
            return
        if kind == 'dest':
            self.walk(t['sub'], a, st, R, k)
            return
        if kind in ('last', 'undefined'):
            return
        if kind == 'ret':
            # Goal-branch wsNode requires the abstract stack to start with
            # .ret (match a, σ.kv | .ret :: _, _ :: kv => ...).
            if not a or a[0][0] != 'ret':
                raise Reject(f"RET at {t['pc']:#x}: top not ret")
            if not st.kv:
                raise Reject(f"RET at {t['pc']:#x}: empty frame")
            kv = st.kv[1:]
            if self.mode == 'check':
                why = ret_ok(st, kv, R)
                if why is not None:
                    raise Reject(f"RET at {t['pc']:#x}: {why}")
            else:
                prov = tuple(prov_of(st, s) for s in kv)
                les = frozenset((j, i) for j in range(len(kv))
                                for i in range(len(st.args))
                                if entails(st.facts, ('le', kv[j], st.args[i])))
                self.retobs.setdefault(self.comp[k], []).append((prov, les))
            return
        if kind == 'branch':
            if len(a) < 2 or len(st.kv) < 2:
                raise Reject(f"JUMPI at {t['pc']:#x}: stack underflow")
            rem = a[2:]
            c, kv = st.kv[1], st.kv[2:]
            self.walk(t['fall'], rem, refine_w(st, c, kv, True), R, k)
            self.walk(t['taken'], rem, refine_w(st, c, kv, False), R, k)
            return
        if kind == 'branchTo':
            if len(a) < 2 or len(st.kv) < 2:
                raise Reject(f"JUMPI at {t['pc']:#x}: stack underflow")
            rem = a[2:]
            c, kv = st.kv[1], st.kv[2:]
            # Goal-branch wsNode looks up es[k] and requires gotoCompat on
            # the stack below target and condition before the old checks.
            tgt = t['target_entry']
            if tgt < 0 or tgt >= len(self.entries):
                raise Reject(f"JUMPI at {t['pc']:#x} to entry {tgt}: out of range")
            if not goto_compat(rem, self.entries[tgt][1]):
                raise Reject(f"JUMPI at {t['pc']:#x} to entry {tgt} "
                             f"(pc {self.entries[tgt][0]:#x}): gotoCompat")
            self.goto(tgt, refine_w(st, c, kv, False),
                      f"JUMPI at {t['pc']:#x}", k)
            self.walk(t['fall'], rem, refine_w(st, c, kv, True), R, k)
            return
        if kind == 'jump':
            if not st.kv:
                raise Reject(f"JUMP at {t['pc']:#x}: empty frame")
            if not a:
                raise Reject(f"JUMP at {t['pc']:#x}: empty abstract stack")
            tgt = t['target_entry']
            if tgt < 0 or tgt >= len(self.entries):
                raise Reject(f"JUMP at {t['pc']:#x} to entry {tgt}: out of range")
            if not goto_compat(a[1:], self.entries[tgt][1]):
                raise Reject(f"JUMP at {t['pc']:#x} to entry {tgt} "
                             f"(pc {self.entries[tgt][0]:#x}): gotoCompat")
            self.goto(tgt, popped_w(st, st.kv[1:]),
                      f"JUMP at {t['pc']:#x}", k)
            return
        if kind == 'callNext':
            ck = t['target_entry']
            if ck < 0 or ck >= len(self.entries):
                raise Reject(f"call at {t['pc']:#x}: entry {ck} out of range")
            if not a or a[0][0] != 'const':
                raise Reject(f"call at {t['pc']:#x}: target not constant")
            if not st.kv:
                raise Reject(f"call at {t['pc']:#x}: empty frame")
            _, eframe, erets = self.entries[ck]
            L = len(eframe)
            kv = st.kv[1:]
            if len(kv) < L:
                raise Reject(f"call at {t['pc']:#x}: frame shorter than callee's")
            cw = kv[:L]
            below = kv[L:]
            Rc = self.get_ret_e(ck)
            want_entry = wst_param(L)
            if self.ann.get(ck) != want_entry:
                raise Reject(f"call at {t['pc']:#x}: entry {ck} annotation "
                             f"is not the callee parameter state")
            if len(Rc.prov) != erets:
                raise Reject(f"call at {t['pc']:#x}: callee return summary has "
                             f"{len(Rc.prov)} words, entry needs {erets}")
            if R.keeps and not Rc.keeps:
                raise Reject(f"call at {t['pc']:#x}: callee does not keep")
            pa = [prov_of(st, s) for s in cw]
            if self.mode == 'infer':
                for s in sorted(Rc.sites, key=repr):
                    self._cover(self.rkey(k), inst_site(pa, list(st.guards), s))
                R = self.get_ret_e(k)
            else:
                for s in sorted(Rc.sites, key=repr):
                    inst = inst_site(pa, list(st.guards), s)
                    if not any(site_covers(q, inst) for q in R.sites):
                        raise Reject(f"call at {t['pc']:#x}: callee site "
                                     f"{show_term(inst[0])} not covered")
            self.goto(ck, popped_w(st, cw), f"call at {t['pc']:#x}", k,
                      check_ret=False, do_compat=False)
            ri = next((i for i, v in enumerate(eframe) if v[0] == 'ret'), None)
            if ri is None:
                return
            aprime = a[1:]
            if ri >= len(aprime) or aprime[ri][0] != 'const':
                raise Reject(f"call at {t['pc']:#x}: continuation not constant")
            # Goal-branch wsNode needs e.frame.length ≤ kv.length.
            if not L <= len(kv):
                raise Reject(f"call at {t['pc']:#x}: callee frame longer")
            st2 = resume_w(st, cw, below, Rc, erets)
            a2 = [('unk',)] * erets + aprime[L:]
            self.walk(t['continuation'], a2, st2, R, k)
            return
        raise Reject(f"unknown node kind {kind}")

    def infer(self, max_rounds: int = 200) -> None:
        # Called entries are pinned to the callee parameter state: Lean's
        # callNext arm requires `A.entry == WSt.param e.frame.length`, and no
        # compat is ever checked at a call.
        self.ann = {0: INIT}
        for ck in self.called:
            self.ann[ck] = wst_param(len(self.entries[ck][1]))
        self.ret_prov = {}
        self.ret_les = {}
        self.sites = {}
        widen: Dict[int, int] = {}
        sys.setrecursionlimit(50000)
        for _ in range(max_rounds):
            self.mode = 'infer'
            self.incoming = {}
            self.incoming_src = {}
            self.retobs = {}
            self._sites_grew = False
            for k in sorted(self.ann):
                if k not in self.trees:
                    continue
                try:
                    self.walk(self.trees[k], list(self.entries[k][1]),
                              self.ann[k], self.get_ret_e(k), k)
                except Reject:
                    pass
            changed = self._sites_grew
            for k, sts in sorted(self.incoming.items()):
                if k == 0 or k in self.called:
                    continue  # pinned annotations
                new = self.ann.get(k)
                try:
                    for s in sts:
                        new = self.join(new, self.canon(s), k, widen)
                except Reject as e:
                    shapes = sorted({(len(s.args),
                                      tuple(sorted(set(s.args)))) for s in sts})
                    srcs = sorted(set(self.incoming_src.get(k, [])))
                    per_src = sorted(
                        {(src, len(s.args), tuple(sorted(set(s.args))))
                         for src, s in zip(self.incoming_src.get(k, []), sts)})
                    key = (k, str(e), str(shapes), str(srcs))
                    if key not in self._noted:
                        self._noted.add(key)
                        self.notes.append(
                            f"entry {k} (pc {self.entries[k][0]:#x}): "
                            f"join failed ({e}); per-source args: {per_src}")
                    if new is None:
                        # Nothing joined at all (cannot happen: joining the
                        # first incoming onto nothing never fails); keep the
                        # old annotation, if any.
                        continue
                    # Keep the agreeing prefix: the entry itself and its
                    # agreeing jumpers still verify; the disagreeing sides
                    # reject (structural conflicts are reported separately).
                if new is not None and new != self.ann.get(k):
                    widen[k] = widen.get(k, 0) + 1
                    self.ann[k] = new
                    changed = True
            for c, obs in sorted(self.retobs.items()):
                # Join the current round's returns from scratch: accumulating
                # onto the old summary lets a stale early-round return poison
                # the summary forever. Rounds with no returns keep the old.
                prov, les = self._join_rets(c, obs)
                if prov != self.ret_prov.get(c) or les != self.ret_les.get(c):
                    self.ret_prov[c] = prov
                    self.ret_les[c] = les
                    changed = True
            if not changed:
                return
        raise Reject("write-site annotation inference did not converge")

    @staticmethod
    def _join_rets(c: int, obs):
        lengths = {len(p) for p, _ in obs}
        if len(lengths) != 1:
            raise Reject(f"component {c}: returns disagree on arity "
                         f"{sorted(lengths)}")
        n = next(iter(lengths))
        first = obs[0][0]
        prov = tuple(first[j] if all(o[0][j] == first[j] for o in obs) else TOP
                     for j in range(n))
        les = frozenset.intersection(*(o[1] for o in obs))
        return prov, les

    def fill_missing(self) -> List[str]:
        """Seed entries the fixpoint never reached: join-only targets from
        fallthrough flows, anything else from a bare frame skeleton. Seeds
        take the union-find entry words, so their args agree with every
        goto edge by construction."""
        self.seeded = {}
        notes = []
        for k in range(len(self.entries)):
            if k in self.ann:
                continue
            n = len(self.entries[k][1])
            if k not in self.trees:
                self.ann[k] = WSt(tuple(range(n)), self.argmap.get(k, ()),
                                   frozenset(), (), (), (), (), (), ())
                self.seeded[k] = "no-tree"
                notes.append(f"entry {k} (pc {self.entries[k][0]:#x}): no tree, "
                             f"bare seed")
                continue
            if k in self.flows:
                new = None
                try:
                    for s in self.flows[k]:
                        new = self.join(new, self.canon(s), k, {})
                except Reject as e:
                    notes.append(f"entry {k} (pc {self.entries[k][0]:#x}): "
                                 f"flow join failed ({e}), agreeing prefix kept")
                    if new is None:
                        new = self.canon(self.flows[k][0])
                if new is not None:
                    self.ann[k] = new
                    self.seeded[k] = "flow"
                    notes.append(f"entry {k} (pc {self.entries[k][0]:#x}): seeded "
                                 f"from {len(self.flows[k])} join flows (no goto)")
                    continue
            self.ann[k] = WSt(tuple(range(n)), self.argmap.get(k, ()),
                              frozenset(), (), (), (), (), (), ())
            self.seeded[k] = "bare"
            notes.append(f"entry {k} (pc {self.entries[k][0]:#x}): unreachable, "
                         f"bare seed")
        return notes

    def rebase(self) -> None:
        """Replace negative canonical entry-word symbols with fresh large
        naturals, per annotation. Lean's `WSt` speaks of `Nat`; the negatives
        are producer-canonical only. The map is bijective within each
        annotation, so every `compat` verdict is preserved; the self-check
        below runs on the rebased annotations, i.e. exactly what is
        emitted."""
        for k, st in self.ann.items():
            negs = set()
            for f in st.facts:
                negs.update(s for s in fact_syms(f) if s < 0)
            negs.update(s for s in st.args if s < 0)
            negs.update(k2 for k2, _ in st.prov if k2 < 0)
            negs.update(s for _, s in st.mem if s < 0)
            negs.update(s for s, _ in st.cur if s < 0)
            negs.update(s for s, _ in st.ub if s < 0)
            negs.update(r for r, _, _ in st.eqs if r < 0)
            if not negs:
                continue
            base = 0
            for f in st.facts:
                for s in fact_syms(f):
                    base = max(base, s)
            for s in list(st.kv) + list(st.args):
                base = max(base, s)
            for k2, _ in st.prov:
                base = max(base, k2)
            for _, s in st.mem:
                base = max(base, s)
            for s, _ in list(st.cur) + list(st.ub):
                base = max(base, s)
            for r, _, _ in st.eqs:
                base = max(base, r)
            m = {s: base - s for s in negs}  # -1 -> base+1, ...
            self.ann[k] = WSt(
                st.kv, tuple(m.get(s, s) for s in st.args),
                frozenset(srename(f, lambda s: m.get(s, s)) for f in st.facts),
                tuple((m.get(k2, k2), t) for k2, t in st.prov),
                tuple((o, m.get(s, s)) for o, s in st.mem),
                tuple((m.get(s, s), t) for s, t in st.cur),
                tuple((m.get(s, s), t) for s, t in st.ub),
                tuple((m.get(r, r), t, u) for r, t, u in st.eqs),
                st.guards)

    def check(self) -> List[str]:
        self.mode = 'check'
        self.stores = []
        errors = []
        for k in range(len(self.entries)):
            if k not in self.trees:
                errors.append(f"entry {k} (pc {self.entries[k][0]:#x}): no tree")
                continue
            if k not in self.ann:
                errors.append(f"entry {k} (pc {self.entries[k][0]:#x}): no annotation")
                continue
            try:
                self.walk(self.trees[k], list(self.entries[k][1]),
                          self.ann[k], self.get_ret_e(k), k)
            except Reject as e:
                tag = getattr(self, "seeded", {}).get(k, "inferred")
                errors.append(f"entry {k} (pc {self.entries[k][0]:#x}) [{tag}]: {e}")
        return errors


# ---- Lean emission ----
FACT_ORDER = {'bnd': 0, 'le': 1, 'lt': 2, 'ltr': 3, 'isz': 4, 'orr': 5, 'rds': 6}


def term_arg_free(t) -> bool:
    k = t[0]
    if k == 'arg':
        return False
    if k in ('cd', 'kecc1'):
        return term_arg_free(t[1])
    if k == 'kecc':
        return term_arg_free(t[1]) and term_arg_free(t[2])
    if k == 'op2':
        return term_arg_free(t[2]) and term_arg_free(t[3])
    return True


def ret_arg_free(R: WRet) -> bool:
    """No returned term, order fact, site slot or guard names an entry word."""
    return (not R.les and all(term_arg_free(t) for t in R.prov)
            and all(term_arg_free(sl) and all(term_arg_free(g[0]) for g in gs)
                    for sl, gs, _ in R.sites))


def lean_fact(f: Tuple) -> str:
    name = 'rdsLe' if f[0] == 'rds' else f[0]
    return "(." + name + "".join(f" {x}" for x in f[1:]) + ")"


def lean_b256(c: int) -> str:
    # a numeral at type `B256` (Jaune's `OfNat B256` instance, `Nat.toB256`)
    return f"0x{c:x}"


def lean_term(t) -> str:
    k = t[0]
    if k == 'top':
        return ".top"
    if k == 'caller':
        return ".caller"
    if k == 'self':
        return ".self"
    if k == 'cd':
        return f"(.cd {lean_term(t[1])})"
    if k == 'const':
        return f"(.const {lean_b256(t[1])})"
    if k == 'arg':
        return f"(.arg {t[1]})"
    if k == 'op2':
        return f"(.op2 .{t[1]} {lean_term(t[2])} {lean_term(t[3])})"
    if k == 'kecc':
        return f"(.kecc {lean_term(t[1])} {lean_term(t[2])})"
    if k == 'kecc1':
        return f"(.kecc1 {lean_term(t[1])})"
    raise Reject(f"cannot emit term {t}")


def lean_guard(g) -> str:
    return f"({lean_term(g[0])}, {lean_b256(g[1])})"


def lean_site(s) -> str:
    slot, guards, non_inc = s
    return (f"⟨{lean_term(slot)}, "
            f"[{', '.join(lean_guard(g) for g in guards)}], "
            f"{'true' if non_inc else 'false'}⟩")


def lean_wret(r: WRet) -> str:
    return (f"⟨[{', '.join(lean_term(t) for t in r.prov)}], "
            f"[{', '.join(f'({j}, {i})' for j, i in sorted(r.les))}], "
            f"{'true' if r.keeps else 'false'}, "
            f"[{', '.join(lean_site(s) for s in sorted(r.sites, key=lean_site))}]⟩")


def lean_wst(st: WSt) -> str:
    # First-match lists (prov/mem/cur/ub/eqs) emit in stored order: Lean's
    # `lookup`/`find?` reads the first entry, so re-sorting could change
    # what the checker sees. Guards are membership-only; stored order is
    # deterministic across builds, so it is kept as well.
    facts = sorted(st.facts, key=lambda f: (FACT_ORDER[f[0]], f[1:]))
    return (f"⟨[{', '.join(str(s) for s in st.kv)}], "
            f"[{', '.join(str(s) for s in st.args)}], "
            f"[{', '.join(lean_fact(f) for f in facts)}], "
            f"[{', '.join(f'({k}, {lean_term(t)})' for k, t in st.prov)}], "
            f"[{', '.join(f'({o}, {s})' for o, s in st.mem)}], "
            f"[{', '.join(f'({s}, {lean_term(t)})' for s, t in st.cur)}], "
            f"[{', '.join(f'({s}, {lean_term(t)})' for s, t in st.ub)}], "
            f"[{', '.join(f'({r}, {lean_term(t)}, {lean_term(u)})' for r, t, u in st.eqs)}], "
            f"[{', '.join(lean_guard(g) for g in st.guards)}]⟩")


def emit_ann(checker: Checker, namespace: str, errors: List[str]) -> str:
    n = len(checker.entries)
    n_ok = n - len([e for e in errors if e.startswith("entry ")])
    lines = [
        "import Blanc.Lift.WriteSite",
        "",
        "/-! GENERATED by scripts/lift/ws_annot.py -- do not edit.",
        "One write-site annotation per certificate entry",
        "(`Blanc/Lift/WriteSite.lean`): the state the entry is entered in and",
        "its function's summary. The producer is untrusted; only the",
        "Lean kernel's `wsCert` over these annotations proves anything.",
        f"Self-check: {n_ok}/{n} entries accepted. -/",
        "",
        f"namespace {namespace}",
        "",
        "open Blanc.Lift.WriteSite",
        "open Blanc.Lift.FreePtr",
        "",
    ]
    # One summary per function component, named once and shared by its
    # entries (the summaries repeat across a component's entries); under the
    # per-entry prototype, one per distinct summary, named by its first entry.
    ret_name: Dict[int, str] = {}
    if SUB_SUMMARY:
        by_text: Dict[str, str] = {}
        for k in range(n):
            text = lean_wret(checker.get_ret_e(k))
            if text not in by_text:
                by_text[text] = f"implWsRet{k}"
                lines += [
                    f"/-- A summary, first of entry {k}. -/",
                    f"def implWsRet{k} : WRet :=",
                    f"  {text}",
                    "",
                ]
            ret_name[k] = by_text[text]
    else:
        comps = sorted(set(checker.comp[k] for k in range(n)))
        for c in comps:
            lines += [
                f"/-- The summary of the function component rooted at entry {c}. -/",
                f"def implWsRet{c} : WRet :=",
                f"  {lean_wret(checker.get_ret(c))}",
                "",
            ]
        ret_name = {k: f"implWsRet{checker.comp[k]}" for k in range(n)}
    lines += [
        "def implWsAnn : List WAnn :=",
        "  [ " + (",\n    ".join(
            f"⟨{lean_wst(checker.ann[k])}, {ret_name[k]}⟩"
            for k in range(n))) if n else "",
        "  ]",
        "",
        f"end {namespace}",
        "",
    ]
    return "\n".join(lines)


CHECK_HEADER = ("GENERATED by scripts/lift/ws_annot.py (registered in "
                "scripts/lift/certificates.json) -- do not edit.")


def lean_module(path: Path) -> str:
    """The Lean module name of a Blanc-relative source path."""
    return ".".join(Path(path).with_suffix("").parts)


def split_parts(costs: List[int], parts: int) -> List[Tuple[int, int]]:
    """Contiguous entry ranges [a, b) of roughly equal total cost."""
    n = len(costs)
    parts = max(1, min(parts, n))
    total = sum(costs)
    bounds, acc, start = [], 0, 0
    for i, c in enumerate(costs):
        acc += c
        left = parts - len(bounds) - 1
        if left > 0 and acc * parts >= total * (len(bounds) + 1) and n - (i + 1) >= left:
            bounds.append((start, i + 1))
            start = i + 1
    bounds.append((start, n))
    return bounds


def emit_checks(checker: Checker, parts: int, namespace: str, cert_ref: str,
                cert_module: str, ann_module: str) -> Dict[str, str]:
    """Kernel-decide modules for `wsCert`: `Check<i>.lean` decides
    `wsEntry cert implWsAnn k` for one contiguous entry range each;
    `Check.lean` chains them (`WriteSiteChain.wsFrom_step`) into
    `ws_rest_0 : wsFrom cert implWsAnn 0 = true`."""
    n = len(checker.entries)
    costs = [checker.cost.get(k, 1) for k in range(n)]
    files: Dict[str, str] = {}
    ranges = split_parts(costs, parts)
    for i, (a, b) in enumerate(ranges):
        lines = [
            "import Blanc.Lift.WriteSiteChain",
            f"import {cert_module}",
            f"import {ann_module}",
            "",
            f"/-! {CHECK_HEADER}",
            f"Entries {a}..{b - 1} of `wsCert {cert_ref} implWsAnn`, each decided by the",
            "kernel (`WriteSiteChain.wsEntry`); `Check.lean` chains them.",
            f"Producer cost proxy for this part: {sum(costs[a:b])}. -/",
            "",
            f"namespace {namespace}",
            "",
            "open Blanc.Lift.WriteSite",
            "",
        ]
        for k in range(a, b):
            lines += [
                f"theorem ws_entry_{k} : wsEntry {cert_ref} implWsAnn {k} = true := by",
                "  decide +kernel",
                "",
            ]
        lines += [f"end {namespace}", ""]
        files[f"Check{i}.lean"] = "\n".join(lines)
    lines = ["import Blanc.Lift.WriteSiteChain"]
    lines += [f"import {namespace}.Check{i}" for i in range(len(ranges))]
    lines += [
        "",
        f"/-! {CHECK_HEADER}",
        "Chains the per-entry decisions of the Check<i> modules over the tails",
        f"of `{cert_ref}.zip implWsAnn`, from the end. -/",
        "",
        f"namespace {namespace}",
        "",
        "open Blanc.Lift.WriteSite",
        "",
        f"theorem ws_rest_{n} : wsFrom {cert_ref} implWsAnn {n} = true :=",
        "  wsFrom_of_le (by decide +kernel)",
        "",
    ]
    for k in range(n - 1, -1, -1):
        lines += [
            f"theorem ws_rest_{k} : wsFrom {cert_ref} implWsAnn {k} = true :=",
            f"  wsFrom_step {k} ws_entry_{k} ws_rest_{k + 1}",
            "",
        ]
    lines += [f"end {namespace}", ""]
    files["Check.lean"] = "\n".join(lines)
    return files


def show_site(s) -> str:
    slot, guards, non_inc = s
    gs = ", ".join(f"{show_term(t)}=0x{c:x}" for t, c in guards)
    return f"slot {show_term(slot)} guards [{gs}] nonInc {non_inc}"


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--row", default="usdc-impl")
    ap.add_argument("--registry", default=str(ROOT / "scripts/lift/certificates.json"))
    ap.add_argument("--ann-out", default=None)
    ap.add_argument("--namespace", default=None)
    ap.add_argument("--max-rounds", type=int, default=200)
    ap.add_argument("--check-dir", default=None,
                    help="also write the kernel-decide Check<i>.lean and Check.lean here")
    ap.add_argument("--check-parts", type=int, default=4)
    ap.add_argument("--sub-summary", action="store_true",
                    help="prototype: per-entry summaries, a goto's target summary covered by the jumper's")
    ap.add_argument("--args-prefix", action="store_true",
                    help="prototype: mirror the proposed prefix relaxation of compat's entry words")
    args = ap.parse_args()
    global ARGS_PREFIX, SUB_SUMMARY
    ARGS_PREFIX = args.args_prefix
    SUB_SUMMARY = args.sub_summary

    t0 = time.time()
    registry = json.loads(Path(args.registry).read_text())
    rows = [r for r in registry["certificates"] if r["id"] == args.row]
    if len(rows) != 1:
        print(f"ws_annot: row {args.row!r} not found", file=sys.stderr)
        return 2
    row = rows[0]
    print(f"ws_annot: rebuilding {args.row} entries/trees with lift.py ...",
          file=sys.stderr)
    try:
        entries, trees, effects, lean_reg, step_inst = load_cert(row)
    except Reject as e:
        print(f"ws_annot: pipeline failed: {e}", file=sys.stderr)
        return 2
    t1 = time.time()
    print(f"ws_annot: {len(entries)} entries, {len(trees)} trees "
          f"({t1 - t0:.1f}s)", file=sys.stderr)

    cert_path = ROOT / row["cert"]
    try:
        check_alignment(entries, cert_path)
    except Reject as e:
        print(f"ws_annot: alignment failed: {e}", file=sys.stderr)
        return 2
    print(f"ws_annot: aligned with committed {row['cert']}", file=sys.stderr)

    checker = Checker(entries, trees, effects, lean_reg, step_inst)
    ncomp = len(set(checker.comp.values()))
    ncalled = len(checker.called)
    keeps_false = sorted(c for c, v in checker.keeps.items() if not v)
    print(f"ws_annot: {ncomp} function components, {ncalled} called entries, "
          f"{len(keeps_false)} non-keeping components", file=sys.stderr)
    if checker.conflicts:
        print(f"ws_annot: {len(checker.conflicts)} args-conflicted "
              f"goto sets (no single annotation satisfies all jumps):",
              file=sys.stderr)
        for r, members, pins in checker.conflicts:
            print(f"ws_annot: conflict set root {r}: entries {members} "
                  f"pins {pins} heads "
                  f"{sorted(set(members) & checker.called)}", file=sys.stderr)
    try:
        checker.infer(max_rounds=args.max_rounds)
    except Reject as e:
        print(f"ws_annot: inference failed: {e}", file=sys.stderr)
        return 2
    t2 = time.time()
    for note in checker.fill_missing():
        print(f"ws_annot: {note}", file=sys.stderr)
    for note in checker.notes:
        print(f"ws_annot: {note}", file=sys.stderr)
    checker.rebase()
    errors = checker.check()
    t3 = time.time()

    n = len(entries)
    print(f"ws_annot: self-check {n - len(errors)}/{n} entries accepted "
          f"(infer {t2 - t1:.1f}s, check {t3 - t2:.1f}s)", file=sys.stderr)
    involved = set()
    for e in errors:
        involved.add(int(e.split()[1]))
    involved |= set(checker.called)
    for k in sorted(involved):
        a = checker.ann.get(k)
        print(f"ws_annot: entry {k} pc 0x{entries[k][0]:x} comp {checker.comp[k]} "
              f"frame {len(entries[k][1])} rets {entries[k][2]} "
              f"ann-args {tuple(a.args) if a is not None else None} "
              f"ann-kv {len(a.kv) if a is not None else None}",
              file=sys.stderr)
    for e in errors:
        print(f"ws_annot rejected: {e}", file=sys.stderr)

    # Per-entry verdicts, then the root sites and every observed SSTORE site
    # (stdout: the unit's report channel).
    err_by_entry = {}
    for e in errors:
        k = int(e.split()[1])
        err_by_entry[k] = e
    for k in range(n):
        pc = entries[k][0]
        if k in err_by_entry:
            print(f"entry {k} pc 0x{pc:x}: REJECT {err_by_entry[k]}")
        else:
            print(f"entry {k} pc 0x{pc:x}: ACCEPT")
    print("ROOT SITES (entry 0 summary):")
    for s in sorted(checker.get_ret_e(0).sites, key=show_site):
        print(f"  {show_site(s)}")
    print("OBSERVED SSTORE SITES (check walk, deduplicated):")
    seen = set()
    for k, pc, obs in checker.stores:
        key = (k, pc, show_site(_canon_site(obs)))
        if key in seen:
            continue
        seen.add(key)
        print(f"  entry {k} pc 0x{pc:x}: {show_site(_canon_site(obs))}")

    namespace = args.namespace or (row["namespace"] + "Ws")
    out = args.ann_out or str(ROOT / "Blanc/Lift/Usdc/ImplWs/Ann.lean")
    text = emit_ann(checker, namespace, errors)
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    Path(out).write_text(text)
    if args.check_dir is not None:
        # the modules live at the namespace's path: <namespace>.Ann, <namespace>.Check<i>
        checks = emit_checks(checker, args.check_parts, namespace,
                             row["namespace"] + ".cert", lean_module(Path(row["cert"])),
                             namespace + ".Ann")
        Path(args.check_dir).mkdir(parents=True, exist_ok=True)
        for name, body in checks.items():
            (Path(args.check_dir) / name).write_text(body)
        print(f"ws_annot: wrote {len(checks)} check modules to {args.check_dir}",
              file=sys.stderr)
    print(f"ws_annot: wrote {out} ({len(text)} bytes, "
          f"{time.time() - t0:.1f}s total)", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
