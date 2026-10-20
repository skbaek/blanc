#!/usr/bin/env python3
"""Free-pointer annotations for a lift certificate (untrusted producer side).

Produces `Ann.lean` for `Blanc/Lift/FreePtr.lean` (`fpCert`): one `Ann`
(entry state plus return summary) per certificate entry, in entry order.
The analysis mirrors `FreePtr.lean` (`fstep`, `opFacts`, `memEff`,
`refineFacts`, `closeLive`, `compat`, `fpNode`) in its R1 revision
(evidence `design/r1-resolution.md` of usdc-neversigner-freepointer-v1) the way
`scripts/lift/lockann.py` mirrors `Blanc/Lift/LockCheck.lean`: it infers one
abstract frame state per entry by a fixpoint over the entry trees, then
re-walks every tree with the inferred annotations exactly as the Lean checker
does and reports the first rejection per entry, if any.

Nothing here is trusted. The Lean kernel decides
`fpCert Impl.cert implFpAnn` over the emitted annotations; a wrong annotation
is a failed build, never a wrong theorem. Facts are kept as sets: every Lean
function over the fact list (`bndOf`, `bnd2`, `entails`, `constOf`,
`freshSym`, `closeLive`) depends only on the set of facts, so the set mirror
decides exactly what the list checker decides.

Entries and trees are computed by `scripts/lift/lift.py` itself (run
in-process with the registry row's arguments; no copies of its pipeline),
and `ninstTransfer` on index patterns plus the annotation symbol map are
reused from `lockann.py` (`labels`, `sym_map`) rather than reimplemented.
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
# Shared symbolic core (facts and stack transfer, amendment A3): moved
# verbatim to symcore.py; re-exported here so existing imports keep working.
from symcore import (
    MAXW, MEMCAP, FPLO, FPCAP, SYMPOS, Reject, syms, rename,
    bnd_of, bnd2, entails, const_of, good, apart_w, not64,
    CMP, cmp_live, close_live, ninst_kind, op_facts,
    learn1, zeros, nonzeros, refine_facts, goto_compat,
    WIDEN_AFTER, WIDEN_HI, WIDEN_LO, widen_hull,
    edge_targets, components, comp_rets,
    load_cert, check_alignment,
)


class FSt:
    """Abstract frame state: symbol per frame word (top first), facts, and the
    symbol of the free-pointer word (None: not known). Mirrors FreePtr.FSt."""

    __slots__ = ('kv', 'facts', 'fp')

    def __init__(self, kv, facts, fp):
        self.kv: Tuple[int, ...] = tuple(kv)
        self.facts: FrozenSet[Tuple] = frozenset(facts)
        self.fp: Optional[int] = fp

    def key(self):
        return (self.kv, self.facts, self.fp)

    def __eq__(self, o):
        return isinstance(o, FSt) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())


INIT = FSt((), frozenset(), None)  # FreePtr.FSt.init

def fresh(kv, facts, fp) -> int:
    m = 0
    for s in kv:
        m = max(m, s)
    if fp is not None:
        m = max(m, fp)
    for f in facts:
        for s in syms(f):
            m = max(m, s)
    return m + 1


def rds_of(fs) -> Optional[int]:
    hs = [f[1] for f in fs if f[0] == 'rds']
    return min(hs) if hs else None


def rds_eff(fs, kind, r) -> Set[Tuple]:
    """FreePtr.rdsEff: what RETURNDATASIZE learns about its result."""
    h = rds_of(fs)
    if kind == ('reg', 'returndatasize') and h is not None:
        return {('bnd', r, 0, h)}
    return set()


def rds_keep(kind, fs):
    """FreePtr.rdsKeep: CALL leaves return data below 2^160; any other exec
    instruction forgets the bound."""
    if kind[0] != 'exec':
        return fs
    rest = frozenset(f for f in fs if f[0] != 'rds')
    return rest | {('rds', MEMCAP - 1)} if kind == ('exec', 'call') else rest


def touched(fs, a, length: int) -> Set[Tuple]:
    """The bound a touched window gives after the step (FreePtr.touched)."""
    below = [a] + [f[1] for f in fs if f[0] == 'le' and f[2] == a]
    return {('bnd', t, 0, max(MEMCAP - length, 0)) for t in below}


STATS: Dict[str, int] = {}


def mem_eff(fs, fp, kind, xs, pc: int):
    """The memory effect (FreePtr.memEff): new fp symbol plus potential facts;
    None rejects. `pc` is only for error messages."""
    STATS[kind[1] if len(kind) == 2 else kind[0]] = \
        STATS.get(kind[1] if len(kind) == 2 else kind[0], 0) + 1
    if kind == ('reg', 'mload'):
        if not xs:
            raise Reject(f"MLOAD at {pc:#x}: empty frame")
        a = xs[0]
        if not64(fs, a):
            return fp, touched(fs, a, 32)
        if fp is None:
            raise Reject(f"MLOAD at {pc:#x}: may read 0x40 (addr bounds "
                         f"{bnd2(fs, a)}) with unknown free pointer")
        if not good(fs, fp):
            raise Reject(f"MLOAD at {pc:#x}: may read 0x40 (addr bounds "
                         f"{bnd2(fs, a)}) with free pointer {fp} outside "
                         f"[0x80, 2^256-2^32] (bounds {bnd2(fs, fp)})")
        return fp, touched(fs, a, 32)
    if kind == ('reg', 'mstore'):
        if len(xs) < 2:
            return fp, set()
        a, v = xs[0], xs[1]
        if const_of(fs, a) == 64:
            # Lean: a store of a value not known good forgets the pointer
            # (fp := none); it does not reject.
            return (v if good(fs, v) else None), touched(fs, a, 32)
        return (fp if apart_w(fs, a, 32) else None), touched(fs, a, 32)
    if kind == ('reg', 'mstore8'):
        if len(xs) < 2:
            return fp, set()
        a = xs[0]
        return (fp if apart_w(fs, a, 1) else None), touched(fs, a, 1)
    if kind in (('reg', 'calldatacopy'), ('reg', 'codecopy'),
                ('reg', 'returndatacopy'), ('reg', 'mcopy')):
        if len(xs) < 3:
            return fp, set()
        d, l = xs[0], xs[2]
        hi, lo = bnd2(fs, l)[1], bnd2(fs, l)[0]
        keep = hi == 0 or apart_w(fs, d, hi)
        return (fp if keep else None), (touched(fs, d, lo) if 1 <= lo else set())
    if kind == ('reg', 'extcodecopy'):
        if len(xs) < 4:
            return fp, set()
        d, l = xs[1], xs[3]
        hi, lo = bnd2(fs, l)[1], bnd2(fs, l)[0]
        keep = hi == 0 or apart_w(fs, d, hi)
        return (fp if keep else None), (touched(fs, d, lo) if 1 <= lo else set())
    if kind in (('exec', 'call'), ('exec', 'callcode')):
        if len(xs) < 7:
            return fp, set()
        o, l = xs[5], xs[6]
        hi = bnd2(fs, l)[1]
        return (fp if (hi == 0 or apart_w(fs, o, hi)) else None), set()
    if kind in (('exec', 'delegatecall'), ('exec', 'staticcall')):
        if len(xs) < 6:
            return fp, set()
        o, l = xs[4], xs[5]
        hi = bnd2(fs, l)[1]
        return (fp if (hi == 0 or apart_w(fs, o, hi)) else None), set()
    return fp, set()


def fstep(op: int, data: bytes, st: FSt, effects, lean_reg, pc: int) -> FSt:
    """One non-jump instruction on the abstract state (FreePtr.fstep)."""
    if 0x5f <= op <= 0x7f:
        r = fresh(st.kv, st.facts, st.fp)
        c = int.from_bytes(data, 'big')
        # Pushes skip closeLive, exactly as in Lean.
        return FSt((r,) + st.kv, st.facts | {('bnd', r, c, c)}, st.fp)
    kind = ninst_kind(op, lean_reg)
    lab = lockann.labels(op, len(st.kv), effects)
    if lab is None:
        raise Reject(f"stack underflow at {pc:#x}")
    if lab.count(None) > 1:
        raise Reject(f"two fresh words at {pc:#x}")
    r = fresh(st.kv, st.facts, st.fp)
    fp2, gas = mem_eff(st.facts, st.fp, kind, list(st.kv), pc)
    # The free-pointer MLOAD names its result by the pointer's own symbol.
    if kind == ('reg', 'mload') and st.kv and const_of(st.facts, st.kv[0]) == 64:
        r2 = fp2 if fp2 is not None else r
    else:
        r2 = r
    kv2 = []
    for l in lab:
        if l is None:
            kv2.append(r2)
        else:
            if l >= len(st.kv):
                raise Reject(f"transfer label {l} out of range at {pc:#x}")
            kv2.append(st.kv[l])
    kv2 = tuple(kv2)
    return FSt(kv2, close_live(kv2, fp2, op_facts(st.facts, kind, list(st.kv), r)
                               | rds_eff(st.facts, kind, r) | gas
                               | rds_keep(kind, st.facts)), fp2)


def refine(st: FSt, c: int, kv, zero: bool) -> FSt:
    kv = tuple(kv)
    return FSt(kv, close_live(kv, st.fp, refine_facts(st.facts, c, zero)), st.fp)


def popped(st: FSt, kv) -> FSt:
    kv = tuple(kv)
    return FSt(kv, close_live(kv, st.fp, st.facts), st.fp)


def sym_map_fp(A: FSt, st: FSt, a: int) -> int:
    """FreePtr.symMap: the incoming symbol an annotation symbol names. The
    free-pointer symbol maps to the incoming free pointer (lockann's sym_map
    is position-only and would misrename it to 0)."""
    if A.fp is not None and A.fp == a:
        return st.fp if st.fp is not None else 0
    for x, s in zip(A.kv, st.kv):
        if x == a:
            return s
    return 0


def compat(st: FSt, A: FSt) -> Optional[str]:
    """The incoming state satisfies the annotation (FreePtr.compat). None fits."""
    if len(st.kv) != len(A.kv):
        return "length"
    m = lambda a: sym_map_fp(A, st, a)  # noqa: E731
    for a, s in zip(A.kv, st.kv):
        if m(a) != s:
            return "partition"
    if A.fp is not None:
        if st.fp is None:
            return "free pointer unknown"
        if any(b == A.fp for b in A.kv):
            return "free pointer aliased in frame"
    for f in A.facts:
        if not entails(st.facts, rename(f, m)):
            return f"fact {f}"
    return None


def resume(sig: FSt, below, R: FSt) -> FSt:
    """The state a call continuation resumes in (FreePtr.resume)."""
    base = fresh(sig.kv, sig.facts, sig.fp)
    m = lambda s: base + s  # noqa: E731
    kv = tuple(m(s) for s in R.kv) + tuple(below)
    fp = None if R.fp is None else m(R.fp)
    return FSt(kv, close_live(kv, fp, {f for f in
                                       {rename(f, m) for f in R.facts} | sig.facts
                                       if f[0] != 'rds'}), fp)


class Checker:
    """Fixpoint inference plus self-check for free-pointer annotations."""

    def __init__(self, entries, trees, effects, lean_reg, step_inst):
        # entries: list of (pc, aval-frame, rets); trees: entry index -> json tree
        self.entries = entries
        self.trees = trees
        self.effects = effects
        self.lean_reg = lean_reg
        self.step_inst = step_inst
        self.ann: Dict[int, FSt] = {}
        self.ret: Dict[int, FSt] = {}
        self.incoming: Dict[int, List[FSt]] = {}
        self.returns: Dict[int, List[FSt]] = {}
        self.flows: Dict[int, List[FSt]] = {}
        self.seeded: Dict[int, str] = {}
        self.cost: Dict[int, int] = {}
        self.mode = 'infer'
        self.comp = self._components()
        self.comp_has_ret = {c: self._comp_has_ret(c)
                             for c in set(self.comp.values())}

    def _comp_has_ret(self, c: int) -> bool:
        """Whether a `.ret` is reachable under the component's return summary:
        follow straight lines, both branch arms, call continuations, joins,
        and intra-component jumps (all walked under the same `R`)."""
        seen_ids: Set[int] = set()
        stack = [self.trees[k] for k in range(len(self.entries))
                 if self.comp[k] == c and k in self.trees]
        while stack:
            u = stack.pop()
            if id(u) in seen_ids:
                continue
            seen_ids.add(id(u))
            kind = u['kind']
            if kind == 'ret':
                return True
            elif kind == 'next':
                stack.append(u['sub'])
            elif kind == 'dest':
                stack.append(u['sub'])
            elif kind == 'branch':
                stack.append(u['fall'])
                stack.append(u['taken'])
            elif kind == 'branchTo':
                stack.append(u['fall'])
                if u['target_entry'] in self.trees:
                    stack.append(self.trees[u['target_entry']])
            elif kind == 'jump':
                if u['target_entry'] in self.trees:
                    stack.append(self.trees[u['target_entry']])
            elif kind == 'join':
                if u['target_entry'] in self.trees:
                    stack.append(self.trees[u['target_entry']])
            elif kind == 'callNext':
                stack.append(u['continuation'])
        return False

    # -- function components: jump/branchTo/join edges share one return summary
    # (shared with the write-site producer via symcore).
    def _components(self) -> Dict[int, int]:
        return components(len(self.entries), self.trees)

    @staticmethod
    def _edge_targets(t) -> List[int]:
        return edge_targets(t)

    def comp_rets(self, c: int) -> int:
        return comp_rets(self.entries, self.comp, c)

    # -- single steps
    def astep(self, pc: int, op: int, data: bytes, a: List[Tuple]) -> List[Tuple]:
        """Mirror of absNinst: lift's own abstract transfer (with the row's
        fold setting), which the pipeline's self-check already validates."""
        out = self.step_inst(op, data, list(a), None)
        if out is None:
            raise Reject(f"abstract transfer fails for {op:#x} at {pc:#x}")
        return [tuple(v) for v in out]

    def goto(self, k: int, st: FSt, what: str, cur: int, is_join: bool = False,
             check_ret: bool = True):
        if k < 0 or k >= len(self.entries):
            raise Reject(f"{what} to entry {k}: out of range")
        if self.mode == 'infer':
            if is_join:
                # Fallthrough joins carry no compat obligation in Lean; their
                # states only seed join-only targets that no goto reaches.
                self.flows.setdefault(k, []).append(st)
            else:
                self.incoming.setdefault(k, []).append(st)
            return
        if is_join:
            return
        A = self.ann.get(k)
        if A is None:
            raise Reject(f"{what} to entry {k}: no annotation")
        why = compat(st, A)
        if why is not None:
            raise Reject(f"{what} to entry {k} "
                         f"(pc {self.entries[k][0]:#x}): {why}")
        if check_ret and self.get_ret(self.comp[k]) != self.get_ret(self.comp[cur]):
            raise Reject(f"{what} to entry {k}: return summary differs")

    def walk(self, t, a: List[Tuple], st: FSt, R: FSt, k: int):
        """Walk tree `t` (json) from AVal stack `a` and state `st`, under the
        current function's return summary `R`. Mirrors FreePtr.fpNode."""
        kind = t['kind']
        if self.mode == 'check':
            # cost proxy for the kernel decide of entry k (Check part balance)
            self.cost[k] = self.cost.get(k, 0) + 1 + len(st.facts)
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
            st2 = fstep(op, data, st, self.effects, self.lean_reg, pc)
            self.walk(t['sub'], a2, st2, R, k)
            return
        if kind == 'dest':
            self.walk(t['sub'], a, st, R, k)
            return
        if kind in ('last', 'undefined'):
            return
        if kind == 'ret':
            # Goal-branch fpNode also requires the abstract stack to start
            # with .ret (match a, σ.kv | .ret :: _, _ :: kv => ...).
            if not a or a[0][0] != 'ret':
                raise Reject(f"RET at {t['pc']:#x}: top not ret")
            if not st.kv:
                raise Reject(f"RET at {t['pc']:#x}: empty frame")
            ret_st = popped(st, st.kv[1:])
            if self.mode == 'check':
                why = compat(ret_st, R)
                if why is not None:
                    raise Reject(f"RET at {t['pc']:#x}: {why}")
            self.returns.setdefault(self.comp[k], []).append(ret_st)
            return
        if kind == 'branch':
            if len(a) < 2 or len(st.kv) < 2:
                raise Reject(f"JUMPI at {t['pc']:#x}: stack underflow")
            rem = a[2:]
            c, kv = st.kv[1], st.kv[2:]
            self.walk(t['fall'], rem, refine(st, c, kv, True), R, k)
            self.walk(t['taken'], rem, refine(st, c, kv, False), R, k)
            return
        if kind == 'branchTo':
            if len(a) < 2 or len(st.kv) < 2:
                raise Reject(f"JUMPI at {t['pc']:#x}: stack underflow")
            rem = a[2:]
            c, kv = st.kv[1], st.kv[2:]
            # Goal-branch fpNode looks up es[k] and requires gotoCompat on
            # the stack below target and condition before the old checks.
            tgt = t['target_entry']
            if tgt < 0 or tgt >= len(self.entries):
                raise Reject(f"JUMPI at {t['pc']:#x} to entry {tgt}: out of range")
            if not goto_compat(rem, self.entries[tgt][1]):
                raise Reject(f"JUMPI at {t['pc']:#x} to entry {tgt} "
                             f"(pc {self.entries[tgt][0]:#x}): gotoCompat")
            self.goto(tgt, refine(st, c, kv, False),
                      f"JUMPI at {t['pc']:#x}", k)
            self.walk(t['fall'], rem, refine(st, c, kv, True), R, k)
            return
        if kind == 'jump':
            if not st.kv:
                raise Reject(f"JUMP at {t['pc']:#x}: empty frame")
            if not a:
                raise Reject(f"JUMP at {t['pc']:#x}: empty abstract stack")
            # Goal-branch fpNode looks up es[k] and requires gotoCompat on
            # the stack below the target before the old conditions.
            tgt = t['target_entry']
            if tgt < 0 or tgt >= len(self.entries):
                raise Reject(f"JUMP at {t['pc']:#x} to entry {tgt}: out of range")
            if not goto_compat(a[1:], self.entries[tgt][1]):
                raise Reject(f"JUMP at {t['pc']:#x} to entry {tgt} "
                             f"(pc {self.entries[tgt][0]:#x}): gotoCompat")
            self.goto(tgt, popped(st, st.kv[1:]),
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
            self.goto(ck, popped(st, kv[:L]), f"call at {t['pc']:#x}", k,
                        check_ret=False)
            ri = next((i for i, v in enumerate(eframe) if v[0] == 'ret'), None)
            if ri is None:
                return
            aprime = a[1:]
            if ri >= len(aprime) or aprime[ri][0] != 'const':
                raise Reject(f"call at {t['pc']:#x}: continuation not constant")
            Rc = self.get_ret(self.comp[ck])
            if len(Rc.kv) != erets:
                raise Reject(f"call at {t['pc']:#x}: callee return summary has "
                             f"{len(Rc.kv)} words, entry needs {erets}")
            # The continuation must be a JUMPDEST block, as Lean's fpNode
            # requires (`.callNext` matches `.dest _`).
            cont = t['continuation']
            while cont['kind'] == 'join':
                cont = self.trees[cont['target_entry']]
            if cont['kind'] != 'dest':
                raise Reject(f"call at {t['pc']:#x}: continuation not a dest block")
            st2 = resume(st, kv[L:], Rc)
            a2 = [('unk',)] * erets + aprime[L:]
            self.walk(t['continuation'], a2, st2, R, k)
            return
        raise Reject(f"unknown node kind {kind}")

    # -- canonical annotations and their join
    @staticmethod
    def canon(st: FSt) -> FSt:
        ren: Dict[int, int] = {}
        for s in st.kv:
            if s not in ren:
                ren[s] = len(ren)
        kv = tuple(ren[s] for s in st.kv)
        # compat requires the annotation's fp symbol to differ from every
        # frame symbol: give it its own index even when the pointer is also on
        # the stack (the equality is forgotten; both keep their bounds).
        fp = None if st.fp is None else len(ren)
        out = set()
        for f in st.facts:
            # Return-data facts never enter annotations (resume drops them).
            if f[0] in ('bnd', 'rds'):
                continue
            if all(s in ren for s in syms(f)):
                out.add(rename(f, lambda s: ren[s]))
            elif st.fp is not None and all(s in ren or s == st.fp for s in syms(f)):
                out.add(rename(f, lambda s: ren[s] if s in ren else fp))
        for s, j in ren.items():
            lo, hi = bnd2(st.facts, s)
            if (lo, hi) != (0, MAXW):
                out.add(('bnd', j, lo, hi))
        if st.fp is not None:
            lo, hi = bnd2(st.facts, st.fp)
            if (lo, hi) != (0, MAXW):
                out.add(('bnd', fp, lo, hi))
        return FSt(kv, out, fp)

    def join(self, a: Optional[FSt], b: FSt, k: int, widen: Dict[int, int]) -> FSt:
        if a is None:
            return b
        if len(a.kv) != len(b.kv):
            raise Reject(f"entry {k}: incoming frames of different lengths")
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
        fresh_idx = max(kv) + 1 if kv else 0
        ea = dict(ma)
        if a.fp is not None and a.fp not in ea:
            ea[a.fp] = fresh_idx
        eb = dict(mb)
        if b.fp is not None and b.fp not in eb:
            eb[b.fp] = fresh_idx
        fa = {rename(f, lambda s: ea[s]) for f in a.facts
              if all(x in ea for x in syms(f))}
        fb = {rename(f, lambda s: eb[s]) for f in b.facts
              if all(x in eb for x in syms(f))}
        fp = ea[a.fp] if (a.fp is not None and b.fp is not None and
                          ea[a.fp] == eb[b.fp]) else None
        facts = {f for f in fa & fb if f[0] != 'bnd'}
        spots = set(kv)
        if fp is not None:
            spots.add(fp)
        for s in spots:
            la, ha = bnd_of(fa, s)
            lb, hb = bnd_of(fb, s)
            lo, hi = min(la, lb), max(ha, hb)
            if widen.get(k, 0) > WIDEN_AFTER and (lo, hi) != (la, ha):
                lo, hi = widen_hull(lo, hi, la, ha)
            if (lo, hi) != (0, MAXW):
                facts.add(('bnd', s, lo, hi))
        return FSt(kv, facts, fp)

    def default_ret(self, c: int) -> FSt:
        n = self.comp_rets(c)
        if self.comp_has_ret.get(c, True):
            # Optimistic walk-time placeholder until the component's returns
            # are observed: a know-nothing placeholder (fp unknown) poisons
            # every caller's continuation, and entry annotations accumulate,
            # so the loss would never be undone.
            return FSt(tuple(range(n)), frozenset({('bnd', n, FPLO, FPLO)}), n)
        # A component with no `.ret` never returns, so every caller's
        # continuation is dead code. Seed a known-good free pointer so the
        # dead continuation walks accept; nothing live ever observes it
        # (no `.ret` node compats against it, and `resume` renames it fresh).
        return FSt(tuple(range(n)), frozenset({('bnd', n, FPLO, FPLO)}), n)

    def get_ret(self, c: int) -> FSt:
        """The stored return summary, else the default (a placeholder for
        walks; only stored summaries are emitted)."""
        r = self.ret.get(c)
        return r if r is not None else self.default_ret(c)

    def infer(self, max_rounds: int = 200) -> None:
        self.ann = {0: INIT}
        # Return slots start empty: joining a know-nothing default with real
        # returns would widen every hull to (0, MAXW). The default serves only
        # as a walk-time placeholder via get_ret until returns are observed.
        self.ret = {}
        widen: Dict[int, int] = {}
        for _ in range(max_rounds):
            self.mode = 'infer'
            self.incoming = {}
            self.returns = {}
            for k in sorted(self.ann):
                if k not in self.trees:
                    continue
                try:
                    self.walk(self.trees[k], list(self.entries[k][1]),
                              self.ann[k], self.get_ret(self.comp[k]), k)
                except Reject:
                    pass
            changed = False
            for k, sts in sorted(self.incoming.items()):
                # Accumulate onto the old annotation (join is monotone
                # weakening, so this converges; joining from scratch
                # oscillates through the ret/entry interdependence).
                new = self.ann.get(k)
                for s in sts:
                    new = self.join(new, self.canon(s), k, widen)
                if k == 0:
                    new = INIT
                if new != self.ann.get(k):
                    widen[k] = widen.get(k, 0) + 1
                    self.ann[k] = new
                    changed = True
            for c, sts in sorted(self.returns.items()):
                # Join the current round's returns from scratch: accumulating
                # onto the old summary lets a stale early-round return (from
                # an annotation since replaced) poison the summary forever
                # (a lost fp never comes back). Rounds with no returns keep
                # the old summary. Entry annotations still accumulate, so the
                # walks driving this stabilize.
                new = None
                for s in sts:
                    new = self.join(new, self.canon(s), ('ret', c), widen)
                if new != self.ret.get(c):
                    widen[('ret', c)] = widen.get(('ret', c), 0) + 1
                    self.ret[c] = new
                    changed = True
            if not changed:
                return
        raise Reject("free-pointer annotation inference did not converge")

    def fill_missing(self) -> List[str]:
        """Seed entries the fixpoint never reached: join-only targets from
        fallthrough flows, anything else from a bare frame skeleton. Seeded
        entries are recorded (their check walks start from states inference
        never used, so their verdicts are inference artifacts until the
        fixpoint reaches them)."""
        self.seeded: Dict[int, str] = {}
        notes = []
        for k in range(len(self.entries)):
            if k in self.ann:
                continue
            if k not in self.trees:
                n = len(self.entries[k][1])
                self.ann[k] = FSt(tuple(range(n)), frozenset(), None)
                self.seeded[k] = "no-tree"
                notes.append(f"entry {k} (pc {self.entries[k][0]:#x}): no tree, "
                             f"bare seed")
                continue
            if k in self.flows:
                new = None
                for s in self.flows[k]:
                    new = self.join(new, self.canon(s), k, {})
                self.ann[k] = new
                self.seeded[k] = "flow"
                notes.append(f"entry {k} (pc {self.entries[k][0]:#x}): seeded "
                             f"from {len(self.flows[k])} join flows (no goto)")
            else:
                n = len(self.entries[k][1])
                self.ann[k] = FSt(tuple(range(n)), frozenset(), None)
                self.seeded[k] = "bare"
                notes.append(f"entry {k} (pc {self.entries[k][0]:#x}): unreachable, "
                             f"bare seed")
        return notes

    def check(self) -> List[str]:
        self.mode = 'check'
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
                          self.ann[k], self.get_ret(self.comp[k]), k)
            except Reject as e:
                tag = getattr(self, "seeded", {}).get(k, "inferred")
                errors.append(f"entry {k} (pc {self.entries[k][0]:#x}) [{tag}]: {e}")
        return errors


# ---- Lean emission (certificate pipeline lives in symcore) ----
FACT_ORDER = {'bnd': 0, 'le': 1, 'lt': 2, 'ltr': 3, 'isz': 4, 'orr': 5, 'rds': 6}


def lean_fact(f: Tuple) -> str:
    name = 'rdsLe' if f[0] == 'rds' else f[0]
    return "(." + name + "".join(f" {x}" for x in f[1:]) + ")"


def lean_fst(st: FSt) -> str:
    facts = sorted(st.facts, key=lambda f: (FACT_ORDER[f[0]], f[1:]))
    fp = f"some {st.fp}" if st.fp is not None else "none"
    return (f"⟨[{', '.join(str(s) for s in st.kv)}], "
            f"[{', '.join(lean_fact(f) for f in facts)}], {fp}⟩")


def emit_ann(checker: Checker, namespace: str, errors: List[str]) -> str:
    n = len(checker.entries)
    n_ok = n - len([e for e in errors if e.startswith("entry ")])
    lines = [
        "import Blanc.Lift.FreePtr",
        "",
        "/-! GENERATED by scripts/lift/fp_annot.py -- do not edit.",
        "One free-pointer annotation per certificate entry",
        "(`Blanc/Lift/FreePtr.lean`): the state the entry is entered in and",
        "its function's return summary. The producer is untrusted; only the",
        "Lean kernel's `fpCert` over these annotations proves anything.",
        "The mirror follows the R1 revision of the checker (`closeLive` closed",
        "three times through comparisons, `learn1` stating learned order facts",
        "as bounds, three `refineFacts` rounds, `Fact.rdsLe` after `CALL`).",
        f"Self-check: {n_ok}/{n} entries accepted. -/",
        "",
        f"namespace {namespace}",
        "",
        "open Blanc.Lift.FreePtr",
        "",
        "def implFpAnn : List Ann :=",
        "  [ " + (",\n    ".join(
            f"⟨{lean_fst(checker.ann[k])}, {lean_fst(checker.get_ret(checker.comp[k]))}⟩"
            for k in range(n))) if n else "",
        "  ]",
        "",
        f"end {namespace}",
        "",
    ]
    return "\n".join(lines)


CHECK_HEADER = ("GENERATED by scripts/lift/fp_annot.py (registered in "
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
    """Kernel-decide modules for `fpCert`: `Check<i>.lean` decides
    `fpEntry cert implFpAnn k` for one contiguous entry range each;
    `Check.lean` chains them (`FreePtrChain.fpFrom_step`) into
    `fp_rest_0 : fpFrom cert implFpAnn 0 = true`."""
    n = len(checker.entries)
    costs = [checker.cost.get(k, 1) for k in range(n)]
    files: Dict[str, str] = {}
    ranges = split_parts(costs, parts)
    for i, (a, b) in enumerate(ranges):
        lines = [
            "import Blanc.Lift.FreePtrChain",
            f"import {cert_module}",
            f"import {ann_module}",
            "",
            f"/-! {CHECK_HEADER}",
            f"Entries {a}..{b - 1} of `fpCert {cert_ref} implFpAnn`, each decided by the",
            "kernel (`FreePtrChain.fpEntry`); `Check.lean` chains them.",
            f"Producer cost proxy for this part: {sum(costs[a:b])}. -/",
            "",
            f"namespace {namespace}",
            "",
            "open Blanc.Lift.FreePtr",
            "",
        ]
        for k in range(a, b):
            lines += [
                f"theorem fp_entry_{k} : fpEntry {cert_ref} implFpAnn {k} = true := by",
                "  decide +kernel",
                "",
            ]
        lines += [f"end {namespace}", ""]
        files[f"Check{i}.lean"] = "\n".join(lines)
    lines = ["import Blanc.Lift.FreePtrChain"]
    lines += [f"import {namespace}.Check{i}" for i in range(len(ranges))]
    lines += [
        "",
        f"/-! {CHECK_HEADER}",
        "Chains the per-entry decisions of the Check<i> modules over the tails",
        f"of `{cert_ref}.zip implFpAnn`, from the end. -/",
        "",
        f"namespace {namespace}",
        "",
        "open Blanc.Lift.FreePtr",
        "",
        f"theorem fp_rest_{n} : fpFrom {cert_ref} implFpAnn {n} = true :=",
        "  fpFrom_of_le (by decide +kernel)",
        "",
    ]
    for k in range(n - 1, -1, -1):
        lines += [
            f"theorem fp_rest_{k} : fpFrom {cert_ref} implFpAnn {k} = true :=",
            f"  fpFrom_step {k} fp_entry_{k} fp_rest_{k + 1}",
            "",
        ]
    lines += [f"end {namespace}", ""]
    files["Check.lean"] = "\n".join(lines)
    return files


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
    args = ap.parse_args()

    t0 = time.time()
    registry = json.loads(Path(args.registry).read_text())
    rows = [r for r in registry["certificates"] if r["id"] == args.row]
    if len(rows) != 1:
        print(f"fp_annot: row {args.row!r} not found", file=sys.stderr)
        return 2
    row = rows[0]
    print(f"fp_annot: rebuilding {args.row} entries/trees with lift.py ...",
          file=sys.stderr)
    try:
        entries, trees, effects, lean_reg, step_inst = load_cert(row)
    except Reject as e:
        print(f"fp_annot: pipeline failed: {e}", file=sys.stderr)
        return 2
    t1 = time.time()
    print(f"fp_annot: {len(entries)} entries, {len(trees)} trees "
          f"({t1 - t0:.1f}s)", file=sys.stderr)

    cert_path = ROOT / row["cert"]
    try:
        check_alignment(entries, cert_path)
    except Reject as e:
        print(f"fp_annot: alignment failed: {e}", file=sys.stderr)
        return 2
    print(f"fp_annot: aligned with committed {row['cert']}", file=sys.stderr)

    sys.setrecursionlimit(50000)
    checker = Checker(entries, trees, effects, lean_reg, step_inst)
    ncomp = len(set(checker.comp.values()))
    print(f"fp_annot: {ncomp} function components", file=sys.stderr)
    try:
        checker.infer(max_rounds=args.max_rounds)
    except Reject as e:
        print(f"fp_annot: inference failed: {e}", file=sys.stderr)
        return 2
    t2 = time.time()
    for note in checker.fill_missing():
        print(f"fp_annot: {note}", file=sys.stderr)
    errors = checker.check()
    t3 = time.time()

    n = len(entries)
    print(f"fp_annot: self-check {n - len(errors)}/{n} entries accepted "
          f"(infer {t2 - t1:.1f}s, check {t3 - t2:.1f}s)", file=sys.stderr)
    for e in errors:
        print(f"fp_annot rejected: {e}", file=sys.stderr)

    namespace = args.namespace or (row["namespace"] + "Fp")
    out = args.ann_out or str(ROOT / "Blanc/Lift/Usdc/ImplFp/Ann.lean")
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
        print(f"fp_annot: wrote {len(checks)} check modules to {args.check_dir}",
              file=sys.stderr)
    facts = sum(len(checker.ann[k].facts) for k in range(n)) + \
        sum(len(checker.get_ret(c).facts) for c in set(checker.comp.values()))
    top_ops = sorted(STATS.items(), key=lambda p: -p[1])[:12]
    print(f"fp_annot: memEff arms hit: {top_ops}", file=sys.stderr)
    n_fp = sum(1 for k in range(n) if checker.ann[k].fp is not None)
    print(f"fp_annot: {n_fp}/{n} entry annotations know the free pointer",
          file=sys.stderr)
    print(f"fp_annot: wrote {out} ({len(text)} bytes, {facts} facts, "
          f"{time.time() - t0:.1f}s total)", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())



