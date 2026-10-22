#!/usr/bin/env python3
"""Shared symbolic core for lift annotation producers (untrusted producer side).

Factored out of `scripts/lift/fp_annot.py` (design amendment A3: the facts
and the stack transfer) and shared by the free-pointer producer and the
write-site producer `scripts/lift/ws_annot.py`. Nothing here is trusted: the
Lean kernel decides each certificate over the emitted annotations.

Contents (moved verbatim from `fp_annot.py`, behavior unchanged):

- interval facts over `FreePtr.Fact` (`bnd_of`, `bnd2`, `entails`,
  `const_of`, `good`, `apart_w`, `not64`);
- the R1 comparison closure (`close_live`) and branch learning
  (`learn1`, `refine_facts`);
- the stack transfer (`ninst_kind`, shared with `lockann.labels`,
  which reuses `lift.py`'s `ninstTransfer` on index patterns) and
  `goto_compat` (`Blanc/Lift/Check.lean`);
- the certificate pipeline (`load_cert`: entries and trees rebuilt with
  `lift.py`'s own code, no copies; `check_alignment` against the
  committed certificate);
- function components over jump/`branchTo`/join edges (entries sharing
  one return summary) and the widening-hull step.

`fp_annot.py`'s free-pointer memory effect (`mem_eff`, `touched`), its
return-data facts (`rds_*`), its state (`FSt`), its `compat`/`resume`,
and its fixpoint/emission stay in `fp_annot.py`: they mirror
`FreePtr.lean` parts the write-site checker does not share
(`WriteSite.lean` reuses only `Fact`, `entails`, `opFacts`,
`refineFacts` and the transfer discipline).
"""

import json
import re
import runpy
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[2]
sys.path.insert(0, str(SCRIPT.parent))
import lockann

MAXW = 2 ** 256 - 1
MEMCAP = 2 ** 160          # MemPotential.memCap (Blanc/Lift/MemPotential.lean)
FPLO = 0x80                # FreePtr.fpLo
FPCAP = 2 ** 256 - 2 ** 32  # FreePtr.fpCap

# Fact encodings (tuples): ('bnd', s, lo, hi) ('le', s, t) ('lt', s, t)
# ('ltr', r, x, y) ('isz', r, s) ('orr', r, x, y) ('rds', h) (FreePtr.Fact.rdsLe:
# the return-data buffer has at most h bytes; no symbols)
SYMPOS = {'bnd': (1,), 'le': (1, 2), 'lt': (1, 2), 'ltr': (1, 2, 3),
          'isz': (1, 2), 'orr': (1, 2, 3), 'rds': ()}


def syms(f: Tuple) -> List[int]:
    return [f[i] for i in SYMPOS[f[0]]]


def rename(f: Tuple, m) -> Tuple:
    return (f[0],) + tuple(m(x) if i in SYMPOS[f[0]] else x
                           for i, x in enumerate(f) if i > 0)


class Reject(Exception):
    pass


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
                hi = min(hi, max(bnd_of(fs, b)[1] - 1, 0))  # Nat truncation
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
        return f in fs or ('lt', f[1], f[2]) in fs or \
            bnd2(fs, f[1])[1] <= bnd2(fs, f[2])[0]
    return f in fs


def const_of(fs, s) -> Optional[int]:
    lo, hi = bnd2(fs, s)
    return lo if lo == hi else None


def good(fs, s) -> bool:
    lo, hi = bnd2(fs, s)
    return FPLO <= lo and hi <= FPCAP


def apart_w(fs, a, len_hi) -> bool:
    return bnd2(fs, a)[1] + len_hi <= 0x40 or 0x60 <= bnd2(fs, a)[0]


def not64(fs, a) -> bool:
    return 64 < bnd2(fs, a)[0] or bnd2(fs, a)[1] < 64


CMP = ('isz', 'ltr', 'orr')


def cmp_live(alive, f) -> bool:
    """A comparison fact is live when its result is, or all its operands are."""
    return alive(f[1]) or all(alive(x) for x in syms(f)[1:])


def close_live(kv, fp, fs):
    """FreePtr.closeLive (R1 revision): keep the facts live in kv/fp, closed
    three times through comparison facts (`growLive`: a live result keeps its
    operands alive; live operands keep the result alive). As a set operation
    this is exactly Lean's filter."""
    alive = set(kv) | ({fp} if fp is not None else set())
    for _ in range(3):
        named = set()
        for f in fs:
            if f[0] in CMP and cmp_live(alive.__contains__, f):
                named.update(syms(f))
        alive = alive | named
    return frozenset(f for f in fs
                     if (cmp_live(alive.__contains__, f) if f[0] in CMP
                         else all(s in alive for s in syms(f))))


# ---- Ninst classification from raw opcodes (FreePtr matches on Ninst) ----
def ninst_kind(op: int, lean_reg: Dict[int, str]):
    """(space, name) with space 'reg'/'exec'; pushes and dup/swap are handled
    by their own arms. Opcodes lift cannot emit (not in LEAN_REG) are
    rejected, exactly as the certificate grammar would."""
    if 0x5f <= op <= 0x7f:
        return ('push',)
    if 0x80 <= op <= 0x8f:
        return ('dup',)
    if 0x90 <= op <= 0x9f:
        return ('swap',)
    if op == 0x59:  # MSIZE: a FreePtr arm lift cannot emit; kept for the mirror
        return ('reg', 'msize')
    s = lean_reg.get(op)
    if s is None:
        raise Reject(f"no Ninst for opcode {op:#x}")
    s = s.strip()
    if s.startswith('.reg'):
        rest = s[len('.reg'):].strip().lstrip('(.').strip()
        return ('reg', rest.split()[0].rstrip(')'))
    if s.startswith('.exec'):
        rest = s[len('.exec'):].strip().lstrip('(.').strip()
        return ('exec', rest.split()[0].rstrip(')'))
    raise Reject(f"cannot classify Ninst '{s}' for opcode {op:#x}")


def op_facts(fs, kind, xs, r) -> Set[Tuple]:
    """The facts about the fresh result r (FreePtr.opFacts)."""
    if kind[0] != 'reg':
        return set()
    name = kind[1]
    x = xs[0] if len(xs) > 0 else None
    y = xs[1] if len(xs) > 1 else None
    if name == 'add' and y is not None:
        lx, hx, ly, hy = bnd2(fs, x)[0], bnd2(fs, x)[1], bnd2(fs, y)[0], bnd2(fs, y)[1]
        if hx + hy <= MAXW:
            return {('bnd', r, lx + ly, hx + hy), ('le', x, r), ('le', y, r)}
        return set()
    if name == 'sub' and y is not None:
        lx, hx, ly, hy = bnd2(fs, x)[0], bnd2(fs, x)[1], bnd2(fs, y)[0], bnd2(fs, y)[1]
        if hy <= lx:
            return {('bnd', r, lx - hy, hx - ly), ('le', r, x)}
        return set()
    if name == 'mul' and y is not None:
        lx, hx, ly, hy = bnd2(fs, x)[0], bnd2(fs, x)[1], bnd2(fs, y)[0], bnd2(fs, y)[1]
        if hx * hy <= MAXW:
            return {('bnd', r, lx * ly, hx * hy)}
        return set()
    if name == 'div' and y is not None:
        lx, hx, ly, hy = bnd2(fs, x)[0], bnd2(fs, x)[1], bnd2(fs, y)[0], bnd2(fs, y)[1]
        if 1 <= ly:
            return {('bnd', r, lx // hy, hx // ly)}
        return {('bnd', r, 0, hx)}
    if name == 'and' and y is not None:
        return {('bnd', r, 0, min(bnd2(fs, x)[1], bnd2(fs, y)[1]))}
    if name == 'or' and y is not None:
        return {('orr', r, x, y)}
    if name == 'shr' and y is not None:
        return {('bnd', r, 0, bnd2(fs, y)[1])}
    if name == 'lt' and y is not None:
        return {('ltr', r, x, y), ('bnd', r, 0, 1)}
    if name == 'gt' and y is not None:
        return {('ltr', r, y, x), ('bnd', r, 0, 1)}
    if name == 'iszero' and x is not None:
        return {('isz', r, x), ('bnd', r, 0, 1)}
    if name == 'eq':
        return {('bnd', r, 0, 1)}
    if name == 'msize':
        return {('bnd', r, 0, MEMCAP)}
    return set()


def learn1(fs, z: Set[int], nz: Set[int]) -> Set[Tuple]:
    """FreePtr.learn1 (R1 revision): an order fact learned is also stated as
    the interval bounds it gives under the current facts."""
    out = set()
    for f in fs:
        if f[0] == 'isz':
            if f[1] in z:
                out.add(('bnd', f[2], 1, MAXW))
            elif f[1] in nz:
                out.add(('bnd', f[2], 0, 0))
        elif f[0] == 'ltr':
            x, y = f[2], f[3]
            if f[1] in z:
                out.add(('le', y, x))
                out.add(('bnd', y, 0, bnd2(fs, x)[1]))
                out.add(('bnd', x, bnd2(fs, y)[0], MAXW))
            elif f[1] in nz:
                out.add(('lt', x, y))
                out.add(('bnd', x, 0, max(bnd2(fs, y)[1] - 1, 0)))
                out.add(('bnd', y, bnd2(fs, x)[0] + 1, MAXW))
        elif f[0] == 'orr':
            if f[1] in z:
                out.add(('bnd', f[2], 0, 0))
                out.add(('bnd', f[3], 0, 0))
    return out


def zeros(r):
    return {f[1] for f in r if f[0] == 'bnd' and f[3] == 0}


def nonzeros(r):
    return {f[1] for f in r if f[0] == 'bnd' and f[2] == 1}


def refine_facts(fs, c: int, zero: bool):
    """FreePtr.refineFacts (R1 revision): three learning rounds."""
    f1 = ({('bnd', c, 0, 0)} if zero else {('bnd', c, 1, MAXW)}) | fs
    r1 = learn1(f1, {c} if zero else set(), set() if zero else {c})
    f2 = r1 | f1
    r2 = learn1(f2, zeros(r1), nonzeros(r1))
    f3 = r2 | f2
    r3 = learn1(f3, zeros(r2), nonzeros(r2))
    return r3 | f3


def goto_compat(a, eframe) -> bool:
    """Blanc/Lift/Check.lean `gotoCompat`: the current abstract stack admits
    the target entry's declared frame. AVal tuples: ('unk',), ('ret',),
    ('const', v) with B256 values as Python ints."""
    if not a and not eframe:
        return True
    if not a or not eframe:
        return False
    x, y = a[0], eframe[0]
    if y[0] == 'unk':
        return goto_compat(a[1:], eframe[1:])
    if x[0] == 'const' and y[0] == 'const':
        return x[1] == y[1] and goto_compat(a[1:], eframe[1:])
    if x[0] == 'ret' and y[0] == 'ret':
        return goto_compat(a[1:], eframe[1:])
    return False


# Producer widening (untrusted; only shapes the annotations): after
# WIDEN_AFTER changes of an entry's hull, a still-changing bound jumps to the
# next threshold instead of being dropped (a dropped loop-index bound loses
# the copy loop's no-wrap fact, and with it the free pointer).
WIDEN_AFTER = 40
WIDEN_HI = (MEMCAP - 32, MEMCAP, 2 ** 255 + 2 ** 160, FPCAP, MAXW)
WIDEN_LO = (FPLO, 0x60, 0x20, 0)


def widen_hull(lo, hi, la, ha):
    """One widening step for a joined bound hull `(lo, hi)` over the old
    hull `(la, ha)`: a still-changing side jumps to the next threshold."""
    if hi != ha:
        hi = next(c for c in WIDEN_HI if c >= hi)
    if lo != la:
        lo = next(c for c in WIDEN_LO if c <= lo)
    return lo, hi


# ---- function components: jump/branchTo/join edges share one return summary ----
def edge_targets(t) -> List[int]:
    out: List[int] = []
    stack = [t]
    while stack:
        u = stack.pop()
        kind = u['kind']
        if kind in ('jump', 'branchTo', 'join'):
            out.append(u['target_entry'])
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


def components(n: int, trees) -> Dict[int, int]:
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

    for k, t in trees.items():
        for tgt in edge_targets(t):
            if 0 <= tgt < n:
                union(k, tgt)
    return {k: find(k) for k in range(n)}


def comp_rets(entries, comp: Dict[int, int], c: int) -> int:
    rets = {entries[k][2] for k in range(len(entries))
            if comp[k] == c}
    if len(rets) != 1:
        raise Reject(f"component {c}: entries disagree on rets {sorted(rets)}")
    return next(iter(rets))


# ---- certificate pipeline (lift.py runs in-process; nothing is copied) ----
def load_cert(row: Dict[str, Any]):
    """Rebuild the registry row's entries and trees with lift.py's own code
    and return (entries, trees, effects, lean_reg, step_inst)."""
    hex_file = ROOT / row["input"]["hex"]
    opts = row.get("options", {})
    if "fold_div_or" in opts and not isinstance(opts["fold_div_or"], bool):
        raise Reject("fold_div_or registry option must be a boolean")
    if opts.get("fold_div_or") is True and opts.get("fold") is not True:
        raise Reject("fold_div_or needs options.fold=true")
    with tempfile.TemporaryDirectory(prefix="lift-annot-") as tmp:
        argv = [str(SCRIPT.parent / "lift.py"),
                "--blanc-root", str(ROOT),
                "--hex", str(hex_file),
                "--sha256", row["input"]["runtime_sha256"],
                "--namespace", row["namespace"],
                "--cert-out", str(Path(tmp) / "Cert.lean"),
                "--header", row.get("header", "GENERATED by scripts/lift/lift.py")]
        if opts.get("fold") is True:
            argv.append("--fold")
        if opts.get("fold_div_or") is True:
            argv.append("--fold-div-or")
        if opts.get("pc") is True:
            argv.append("--pc")
        if opts.get("decide_jumpi") is True:
            argv.append("--decide-jumpi")
        for option in ("code_import", "code_ref"):
            if opts.get(option) is not None:
                argv += ["--" + option.replace("_", "-"), opts[option]]
        saved = sys.argv
        sys.argv = argv
        try:
            ns = runpy.run_path(str(SCRIPT.parent / "lift.py"),
                                run_name="lift_pipeline")
        finally:
            sys.argv = saved

    def frame(e):
        out = []
        for v in e["frame"]:
            if v.startswith('const'):
                out.append(('const', int(v[6:-1], 16)))
            elif v == 'ret':
                out.append(('ret',))
            else:
                out.append(('unk',))
        return out

    entries = [(int(e["pc"], 16), frame(e), e["rets"]) for e in ns["json_entries"]]
    trees = {int(k): v for k, v in ns["json_trees"].items()}
    return entries, trees, ns["OPCODE_EFFECTS"], ns["LEAN_REG"], ns["step_inst"]


def check_alignment(entries, cert_path: Path):
    """The emitted annotations index the committed certificate: pcs, frames
    and rets must match its entry list exactly, in order."""
    lines = [l for l in cert_path.read_text().splitlines()
             if re.match(r"^  \(⟨0x[0-9a-f]+, ", l)]
    if len(lines) != len(entries):
        raise Reject(f"entry count {len(entries)} != committed {len(lines)}")
    for i, (line, (pc, fr, rets)) in enumerate(zip(lines, entries)):
        m = re.match(r"^  \(⟨(0x[0-9a-f]+), (\[[^\]]*\]), (\d+)⟩, (t_\w+)\),?$",
                     line)
        if m is None:
            raise Reject(f"cannot read committed certificate entry {i}")
        cpc, cfr, crets = m.group(1), m.group(2), int(m.group(3))
        want = "[" + ", ".join(
            ".unk" if v[0] == 'unk' else ".ret" if v[0] == 'ret'
            else f"(.const (Nat.toB256 0x{v[1]:x}))" for v in fr) + "]"
        if int(cpc, 16) != pc or cfr != want or crets != rets:
            raise Reject(f"entry {i} differs from committed certificate "
                         f"(pipeline {pc:#x} {fr} {rets} vs committed {line})")
