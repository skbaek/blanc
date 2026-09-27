"""Reentrancy-lock annotations for a lift certificate (untrusted producer side).

`lift.py --lock-spec FILE --lock-ann-out FILE --lock-check-out FILE` calls
`generate` on the certificate it has just built.  The analysis is a mirror of
`Blanc/Lift/LockCheck.lean` (`lockNode`, `lstep`, `refine`, `compat`, ...):
it infers one abstract lock state per certificate entry by a fixpoint over
the entry trees, then re-walks every tree with the inferred annotations
exactly as the Lean checker does and reports the first rejection, if any.

Nothing here is trusted.  The Lean kernel decides `lockCert` over the emitted
annotations; a wrong annotation is a failed build, never a wrong theorem.
Facts are kept as sets: every Lean function over the fact list
(`bndOf`, `bnd2`, `entails`, `contains`, `filter`, `freshSym`) depends only on
the set of facts, so the set mirror decides exactly what the list checker
decides.
"""

from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple

MAXW = 2 ** 256 - 1

# Fact encodings (tuples): ('bnd', s, lo, hi) ('nsl', s) ('lt', s, t) ('le', s, t)
# ('gt', r, s, k) ('isz', r, s) ('xor', r, s, t) ('lockv', s) ('lockeq', r)
SYMPOS = {'bnd': (1,), 'nsl': (1,), 'lt': (1, 2), 'le': (1, 2), 'gt': (1, 2),
          'isz': (1, 2), 'xor': (1, 2, 3), 'lockv': (1,), 'lockeq': (1,)}


def syms(f: Tuple) -> List[int]:
    return [f[i] for i in SYMPOS[f[0]]]


def rename(f: Tuple, m) -> Tuple:
    return (f[0],) + tuple(m(x) if i in SYMPOS[f[0]] else x for i, x in enumerate(f) if i > 0)


class Reject(Exception):
    pass


class State:
    __slots__ = ('kv', 'facts', 'passed', 'setnow', 'nomut')

    def __init__(self, kv, facts, passed, setnow, nomut):
        self.kv: Tuple[int, ...] = tuple(kv)
        self.facts: FrozenSet[Tuple] = frozenset(facts)
        self.passed, self.setnow, self.nomut = passed, setnow, nomut

    def key(self):
        return (self.kv, self.facts, self.passed, self.setnow, self.nomut)

    def __eq__(self, o):
        return isinstance(o, State) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())


INIT = State((), (), False, False, True)


def bnd_of(fs, s):
    lo, hi = 0, MAXW
    for f in fs:
        if f[0] == 'bnd' and f[1] == s:
            lo, hi = max(lo, f[2]), min(hi, f[3])
    return lo, hi


def bnd2(fs, s):
    lo, hi = bnd_of(fs, s)
    for f in fs:
        if f[0] == 'lt':
            a, b = f[1], f[2]
            if a == s:
                hi = min(hi, max(bnd_of(fs, b)[1] - 1, 0))
            elif b == s:
                lo = max(lo, bnd_of(fs, a)[0] + 1)
        elif f[0] == 'le':
            a, b = f[1], f[2]
            if a == s:
                hi = min(hi, bnd_of(fs, b)[1])
            elif b == s:
                lo = max(lo, bnd_of(fs, a)[0])
    return lo, hi


def entails(fs, f) -> bool:
    k = f[0]
    if k == 'bnd':
        lo, hi = bnd2(fs, f[1])
        return f[2] <= lo and hi <= f[3]
    if k == 'lt':
        return f in fs or bnd2(fs, f[1])[1] < bnd2(fs, f[2])[0]
    if k == 'le':
        return f in fs or ('lt', f[1], f[2]) in fs or bnd2(fs, f[1])[1] <= bnd2(fs, f[2])[0]
    return f in fs


def const_of(fs, s) -> Optional[int]:
    lo, hi = bnd2(fs, s)
    return lo if lo == hi else None


def fresh(kv, fs) -> int:
    m = 0
    for s in kv:
        m = max(m, s)
    for f in fs:
        for s in syms(f):
            m = max(m, s)
    return m + 1


def live(kv, f) -> bool:
    ks = set(kv)
    return all(s in ks for s in syms(f))


def filt(kv, fs):
    ks = set(kv)
    return frozenset(f for f in fs if all(s in ks for s in syms(f)))


# ---- ninstTransfer on index patterns: output labels (input index or None)
def labels(op: int, n: int, effects) -> Optional[List[Optional[int]]]:
    if 0x80 <= op <= 0x8f:
        i = op - 0x80
        return None if i >= n else [i] + list(range(n))
    if 0x90 <= op <= 0x9f:
        i = op - 0x8f
        if i >= n:
            return None
        lab = list(range(n))
        lab[0], lab[i] = lab[i], lab[0]
        return lab
    _, pops, pushes = effects[op]
    if n < pops:
        return None
    return [None] * pushes + list(range(pops, n))


class Checker:
    def __init__(self, spec: Dict[str, Any], entries, trees, effects):
        self.slot = spec['slot']
        self.locked = spec['locked']
        self.bodies = set(spec['bodies'])
        self.mut = set(spec['mutBodies'])
        self.sets = set(spec['setPcs'])
        self.rels = set(spec['releasePcs'])
        self.entries = entries          # list of (pc, frame(list of 'unk'/'ret'/('const',v)), rets)
        self.trees = trees              # entry index -> json tree
        self.effects = effects
        self.ann: Dict[int, State] = {}
        self.incoming: Dict[int, List[State]] = {}
        self.mode = 'infer'

    # -- lstep
    def excluded(self, fs, k) -> bool:
        lo, hi = bnd2(fs, k)
        return not (lo <= self.slot <= hi) or ('nsl', k) in fs

    def add_facts(self, fs, kv, x, y, r):
        out = set()
        (lx, hx), (ly, hy) = bnd2(fs, x), bnd2(fs, y)
        if hx + hy <= MAXW:
            out.add(('bnd', r, lx + ly, hx + hy))
        if const_of(fs, y) == 1:
            out |= {('le', r, t) for t in kv if entails(fs, ('lt', x, t))}
        if const_of(fs, x) == 1:
            out |= {('le', r, t) for t in kv if entails(fs, ('lt', y, t))}
        return out

    def op_facts(self, fs, kv, op, r):
        x = kv[0] if len(kv) > 0 else None
        y = kv[1] if len(kv) > 1 else None
        if op == 0x54 and x is not None:
            return {('lockv', r)} if const_of(fs, x) == self.slot else set()
        if op == 0x14 and y is not None:
            if (('lockv', x) in fs and const_of(fs, y) == self.locked) or \
               (('lockv', y) in fs and const_of(fs, x) == self.locked):
                return {('lockeq', r)}
            return set()
        if op == 0x20:
            return {('nsl', r)}
        if op == 0x01 and y is not None:
            return self.add_facts(fs, kv, x, y, r)
        if op == 0x11 and y is not None:
            k = const_of(fs, y)
            return {('gt', r, x, k)} if k is not None else set()
        if op == 0x15 and x is not None:
            return {('isz', r, x)}
        if op == 0x18 and y is not None:
            return {('xor', r, x, y)}
        return set()

    def eff_setnow(self, pc, op, st: State) -> bool:
        if op == 0x55:
            if len(st.kv) < 2:
                raise Reject(f"SSTORE at {pc:#x}: stack")
            k, v = st.kv[0], st.kv[1]
            if self.excluded(st.facts, k):
                return st.setnow
            if const_of(st.facts, k) == self.slot and st.passed and \
                    (pc in self.rels or (st.nomut and pc in self.sets)):
                return const_of(st.facts, v) == self.locked
            raise Reject(f"SSTORE at {pc:#x}: key {k} may be the lock slot "
                         f"(bounds {bnd2(st.facts, k)}, passed={st.passed}, noMut={st.nomut})")
        if op in (0xf1, 0xfa):
            return False
        return st.setnow

    def lstep(self, pc, op, data: bytes, st: State) -> State:
        if 0x5f <= op <= 0x7f:
            r = fresh(st.kv, st.facts)
            c = int.from_bytes(data, 'big')
            return State((r,) + st.kv, st.facts | {('bnd', r, c, c)}, st.passed, st.setnow, st.nomut)
        if op in (0xf0, 0xf2, 0xf4, 0xf5):
            raise Reject(f"forbidden opcode {op:#x} at {pc:#x}")
        lab = labels(op, len(st.kv), self.effects)
        if lab is None:
            raise Reject(f"stack underflow at {pc:#x}")
        if lab.count(None) > 1:
            raise Reject(f"two fresh words at {pc:#x}")
        r = fresh(st.kv, st.facts)
        kv2 = tuple(st.kv[i] if i is not None else r for i in lab)
        setnow = self.eff_setnow(pc, op, st)
        facts = filt(kv2, self.op_facts(st.facts, st.kv, op, r) | st.facts)
        return State(kv2, facts, st.passed, setnow, st.nomut)

    # -- branches, joins
    def refine(self, st: State, c, kv, zero: bool) -> State:
        fs = st.facts
        new = set()
        for f in fs:
            if f[0] == 'gt' and f[1] == c:
                new.add(('bnd', f[2], 0, f[3]) if zero else ('bnd', f[2], f[3] + 1, MAXW))
            elif f[0] == 'isz' and f[1] == c:
                new.add(('bnd', f[2], 1, MAXW) if zero else ('bnd', f[2], 0, 0))
            elif f[0] == 'xor' and f[1] == c and not zero:
                s, t = f[2], f[3]
                if entails(fs, ('le', s, t)):
                    new.add(('lt', s, t))
                if entails(fs, ('le', t, s)):
                    new.add(('lt', t, s))
        passed = st.passed or (zero and ('lockeq', c) in fs)
        return State(kv, filt(kv, new | fs), passed, st.setnow, st.nomut)

    @staticmethod
    def popped(st: State, kv) -> State:
        return State(kv, filt(kv, st.facts), st.passed, st.setnow, st.nomut)

    @staticmethod
    def resume(saved: State, rets: int) -> State:
        r0 = fresh(saved.kv, saved.facts)
        return State(tuple(r0 + i for i in range(rets)) + saved.kv, saved.facts, saved.passed, False, False)

    @staticmethod
    def sym_map(A, kv):
        m = {}
        for a, s in zip(A, kv):
            if a not in m:
                m[a] = s
        return lambda a: m.get(a, 0)

    def compat(self, st: State, A: State) -> Optional[str]:
        if len(st.kv) != len(A.kv):
            return "length"
        m = self.sym_map(A.kv, st.kv)
        for a, s in zip(A.kv, st.kv):
            if m(a) != s:
                return "partition"
        if (A.passed and not st.passed) or (A.setnow and not st.setnow) or (A.nomut and not st.nomut):
            return f"flags (ann {A.passed},{A.setnow},{A.nomut} vs {st.passed},{st.setnow},{st.nomut})"
        for f in A.facts:
            g = rename(f, m)
            if not entails(st.facts, g):
                return f"fact {f}"
        return None

    def goto(self, k, st: State, what: str):
        if self.mode == 'infer':
            self.incoming.setdefault(k, []).append(st)
            return
        A = self.ann.get(k)
        if A is None:
            raise Reject(f"{what} to entry {k}: no annotation")
        why = self.compat(st, A)
        if why is not None:
            raise Reject(f"{what} to entry {k} (pc {self.entries[k][0]:#x}): {why}")

    def visit(self, pc, st: State) -> State:
        if pc in self.mut:
            st = State(st.kv, st.facts, st.passed, st.setnow, False)
        if pc in self.bodies and not st.passed:
            raise Reject(f"body start {pc:#x} without a passed lock check")
        if pc in self.mut and not st.setnow:
            raise Reject(f"mutating body start {pc:#x} without the lock set")
        return st

    def walk(self, t, a_len: int, st: State):
        """Walk tree `t` (json) from state `st`; iterative on straight-line code."""
        while True:
            kind = t['kind']
            if kind == 'join':
                t = self.trees[t['target_entry']]
                continue
            pc = t['pc']
            st = self.visit(pc, st)
            if kind == 'next':
                st = self.lstep(pc, int(t['op'], 16), bytes.fromhex(t['data']), st)
                t = t['sub']
                continue
            if kind == 'dest':
                t = t['sub']
                continue
            if kind == 'last':
                if int(t['op'], 16) == 0xff:
                    raise Reject(f"SELFDESTRUCT at {pc:#x}")
                return
            if kind in ('ret', 'undefined'):
                return
            if kind == 'branch':
                c, kv = st.kv[1], st.kv[2:]
                self.walk(t['fall'], a_len, self.refine(st, c, kv, True))
                t, st = t['taken'], self.refine(st, c, kv, False)
                continue
            if kind == 'branchTo':
                c, kv = st.kv[1], st.kv[2:]
                self.goto(t['target_entry'], self.refine(st, c, kv, False), f"JUMPI at {pc:#x}")
                t, st = t['fall'], self.refine(st, c, kv, True)
                continue
            if kind == 'jump':
                self.goto(t['target_entry'], self.popped(st, st.kv[1:]), f"JUMP at {pc:#x}")
                return
            if kind == 'callNext':
                k = t['target_entry']
                _, frame, rets = self.entries[k]
                L = len(frame)
                kv = st.kv[1:]
                self.goto(k, self.popped(st, kv[:L]), f"call at {pc:#x}")
                if 'ret' not in frame:
                    return
                saved = State(kv[L:], filt(kv[L:], st.facts), st.passed, False, False)
                t, st = t['continuation'], self.resume(saved, rets)
                continue
            raise Reject(f"unknown node kind {kind}")

    # -- canonical annotations and their join
    @staticmethod
    def canon(st: State) -> State:
        ren: Dict[int, int] = {}
        for j, s in enumerate(st.kv):
            ren.setdefault(s, j)
        kv = tuple(ren[s] for s in st.kv)
        out = set()
        for f in st.facts:
            if f[0] == 'bnd':
                continue
            if all(s in ren for s in syms(f)):
                out.add(rename(f, lambda s: ren[s]))
        for s, j in ren.items():
            lo, hi = bnd2(st.facts, s)
            if (lo, hi) != (0, MAXW):
                out.add(('bnd', j, lo, hi))
        return State(kv, out, st.passed, st.setnow, st.nomut)

    def join(self, a: Optional[State], b: State, k: int, widen: Dict[int, int]) -> State:
        if a is None:
            return b
        if len(a.kv) != len(b.kv):
            raise Reject(f"entry {k}: incoming frames of different lengths")
        first: Dict[Tuple[int, int], int] = {}
        kv = []
        for j, pair in enumerate(zip(a.kv, b.kv)):
            first.setdefault(pair, j)
            kv.append(first[pair])
        ma: Dict[int, int] = {}
        mb: Dict[int, int] = {}
        for j, s in enumerate(kv):
            ma.setdefault(a.kv[j], s)
            mb.setdefault(b.kv[j], s)
        fa = {rename(f, lambda s: ma[s]) for f in a.facts if all(x in ma for x in syms(f))}
        fb = {rename(f, lambda s: mb[s]) for f in b.facts if all(x in mb for x in syms(f))}
        facts = {f for f in fa & fb if f[0] != 'bnd'}
        for s in set(kv):
            la, ha = bnd_of(fa, s)
            lb, hb = bnd_of(fb, s)
            lo, hi = min(la, lb), max(ha, hb)
            if widen.get(k, 0) > 8 and (lo, hi) != (la, ha):
                continue
            if (lo, hi) != (0, MAXW):
                facts.add(('bnd', s, lo, hi))
        return State(kv, facts, a.passed and b.passed, a.setnow and b.setnow, a.nomut and b.nomut)

    def infer(self, max_rounds: int = 200) -> None:
        self.ann = {0: INIT}
        widen: Dict[int, int] = {}
        for _ in range(max_rounds):
            self.mode = 'infer'
            self.incoming = {}
            for k in sorted(self.ann):
                try:
                    self.walk(self.trees[k], len(self.entries[k][1]), self.ann[k])
                except Reject:
                    pass
            changed = False
            for k, sts in sorted(self.incoming.items()):
                new = self.ann.get(k)
                for s in sts:
                    new = self.join(new, self.canon(s), k, widen)
                if k == 0:
                    new = INIT
                if new != self.ann.get(k):
                    widen[k] = widen.get(k, 0) + 1
                    self.ann[k] = new
                    changed = True
            if not changed:
                return
        raise Reject("lock annotation inference did not converge")

    def check(self) -> List[str]:
        self.mode = 'check'
        errors = []
        for k in range(len(self.entries)):
            if k not in self.ann:
                self.ann[k] = State(tuple(range(len(self.entries[k][1]))), (), False, False, False)
        for k in range(len(self.entries)):
            try:
                self.walk(self.trees[k], len(self.entries[k][1]), self.ann[k])
            except Reject as e:
                errors.append(f"entry {k} (pc {self.entries[k][0]:#x}): {e}")
        return errors


def lean_fact(f: Tuple) -> str:
    return "." + f[0] + " " + " ".join(str(x) for x in f[1:])


def lean_state(st: State) -> str:
    facts = sorted(st.facts, key=lambda f: (f[0], f[1:]))
    b = lambda x: "true" if x else "false"
    return (f"⟨[{', '.join(str(s) for s in st.kv)}], "
            f"[{', '.join('(' + lean_fact(f) + ')' for f in facts)}], "
            f"{b(st.passed)}, {b(st.setnow)}, {b(st.nomut)}⟩")
