import Blanc.Lift.FreePtr
import Blanc.Lift.CheckMem

/-! ## W1  `Blanc/Lift/WriteSite.lean` (checker; contract-neutral) -/

namespace Blanc.Lift.WriteSite

open Jaune AbstractStackSafety
open Blanc.Lift.FreePtr (Fact)

/-- The binary operations a provenance term records.  The first argument is the instruction's
top operand, as in Jaune's `applyBinary`. -/
inductive Op2 : Type
  | add | sub | mul | div | and | or | shl | shr | exp
deriving DecidableEq

def Op2.eval : Op2 → B256 → B256 → B256
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .and, x, y => B256.and x y
  | .or, x, y => B256.or x y
  | .shl, x, y => y <<< x.toNat
  | .shr, x, y => y >>> x.toNat
  | .exp, x, y => B256.bexp x y

/-- Commutative operations: their constant operand is kept on the right. -/
def Op2.comm : Op2 → Bool
  | .add | .mul | .and | .or => true
  | _ => false

def Op2.ofRinst : Rinst → Option Op2
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .and => some .and
  | .or => some .or
  | .shl => some .shl
  | .shr => some .shr
  | .exp => some .exp
  | _ => none

/-- **Provenance terms**: what a word is, as a function of the frame's constants (caller, own
address, calldata) and of the current function's entry words (`arg i`, top first).  `top` is
"anything": an `SLOAD` result, a call's return, a value the checker does not follow (the brief's
`ext`).  The smart constructors below keep `top` absorbing. -/
inductive Term : Type
  | top
  | caller
  | self
  /-- The calldata word at a byte offset. -/
  | cd (off : Term)
  | const (c : B256)
  | arg (i : Nat)
  | op2 (o : Op2) (a b : Term)
  /-- solc's two-word hash, `keccak256(key ‖ base)` (`Blanc.Lift.mapSlot`). -/
  | kecc (key base : Term)
  /-- The hash of one word (solc's dynamic-array and long-string data slots). -/
  | kecc1 (w : Term)
deriving DecidableEq

/-- The term mentions no `top`. -/
def Term.known : Term → Bool
  | .top => false
  | .cd t => t.known
  | .op2 _ a b => a.known && b.known
  | .kecc a b => a.known && b.known
  | .kecc1 t => t.known
  | _ => true

def mkCd (t : Term) : Term := if t.known then .cd t else .top
def mkKecc (a b : Term) : Term := if a.known && b.known then .kecc a b else .top
def mkKecc1 (t : Term) : Term := if t.known then .kecc1 t else .top

/-- `AND` with the mask it already carries is the same word (solc re-masks addresses). -/
def mkOp2' (o : Op2) (a b : Term) : Term :=
  match o, a, b with
  | .and, .op2 .and t (.const m), .const m' =>
    if m = m' then .op2 .and t (.const m) else .op2 .and a b
  | o, a, b => .op2 o a b

/-- A binary node: constants fold, `top` absorbs, a commutative constant goes right. -/
def mkOp2 (o : Op2) (a b : Term) : Term :=
  if a.known && b.known then
    match a, b with
    | .const x, .const y => .const (o.eval x y)
    | .const x, b => if o.comm then mkOp2' o b (.const x) else .op2 o (.const x) b
    | a, b => mkOp2' o a b
  else .top

/-- Instantiate a callee's term at a call site: `arg i` becomes the caller's term for the
callee's `i`-th entry word. -/
def Term.subst (pa : List Term) : Term → Term
  | .arg i => pa.getD i .top
  | .cd t => mkCd (t.subst pa)
  | .op2 o a b => mkOp2 o (a.subst pa) (b.subst pa)
  | .kecc a b => mkKecc (a.subst pa) (b.subst pa)
  | .kecc1 t => mkKecc1 (t.subst pa)
  | t => t

/-- A storage write site: the slot's term, the frame guards known there (`⟦t⟧ = c`, learned from
`EQ` branches, e.g. the dispatcher's selector), and whether the write provably never increases
the slot (`v ≤` the slot's current value). -/
structure Site : Type where
  slot : Term
  guards : List (Term × B256)
  nonInc : Bool
deriving DecidableEq

/-- The listed site `s` covers the observed site `o`: the same slot (or `top`), a subset of its
guards, and no stronger write claim. -/
def Site.covers (s o : Site) : Bool :=
  (s.slot == .top || s.slot == o.slot) && s.guards.all (o.guards.contains ·) &&
    (!s.nonInc || o.nonInc)

/-- A function's summary, over its entry words `arg i`: its returned words' terms (top first),
order facts `(j, i)`: returned word `j ≤` entry word `i`, whether it keeps the executing
account's storage (no `SSTORE`, no call but `STATICCALL`, only keeping callees), and the write
sites of it and its callees. -/
structure WRet : Type where
  prov : List Term
  les : List (Nat × Nat)
  keeps : Bool
  sites : List Site
deriving DecidableEq

/-- An abstract frame state.  `kv`: a symbol per frame word (top first); `args`: the symbols of
the current function's entry words; `facts`: the free-pointer checker's facts (F1, meaning F3a);
`prov`: a symbol's term (absent: `top`); `mem`: the symbol of the word at a constant offset;
`cur`: `(s, T)`, the slot `⟦T⟧` of the executing account holds `s` now; `ub`: `(s, T)`, `s ≤`
that slot now; `eqs`: `(r, t, u)`, `r = EQ` of two words with terms `t`, `u`; `guards`: frame facts `⟦t⟧ = c`. -/
structure WSt : Type where
  kv : List Nat
  args : List Nat
  facts : List Fact
  prov : List (Nat × Term)
  mem : List (Nat × Nat)
  cur : List (Nat × Term)
  ub : List (Nat × Term)
  eqs : List (Nat × Term × Term)
  guards : List (Term × B256)
deriving DecidableEq

/-- Entry `k`'s annotation: the state it is entered in and its function's summary (loop heads
and join points share their function's summary). -/
structure WAnn : Type where
  entry : WSt
  ret : WRet
deriving DecidableEq

/-- The state a callee is entered in: its `n` frame words are its parameters. -/
def WSt.param (n : Nat) : WSt :=
  let ks := (List.range n).map (· + 1)
  ⟨ks, ks, [], (List.range n).map (fun i => (i + 1, .arg i)), [], [], [], [], []⟩

def WSt.init : WSt := WSt.param 0

def WSt.provOf (σ : WSt) (s : Nat) : Term := (σ.prov.lookup s).getD .top

def WSt.syms (σ : WSt) : List Nat :=
  σ.kv ++ σ.args ++ σ.facts.flatMap Fact.syms ++ σ.prov.map Prod.fst ++ σ.mem.map Prod.snd ++
    σ.cur.map Prod.fst ++ σ.ub.map Prod.fst ++ σ.eqs.map Prod.fst

def WSt.fresh (σ : WSt) : Nat := σ.syms.foldr max 0 + 1

/-- The symbols a state keeps facts about: frame words, entry words, memory words and the
symbols of current storage values. -/
def WSt.liveSyms (σ : WSt) : List Nat :=
  σ.kv ++ σ.args ++ σ.mem.map Prod.snd ++ σ.cur.map Prod.fst ++ σ.ub.map Prod.fst

/-- One round of the comparison-chain closure: the operands of a comparison fact whose result
is kept stay, so that a branch can still learn through `ISZERO(LT(x, y))` after both results were
consumed (the free-pointer checker's `live` drops them; see the co-design amendments). -/
def closeLive (fs : List Fact) (L : List Nat) : List Nat :=
  L ++ fs.flatMap fun f => match f with
    | .isz r s => if L.contains r then [s] else []
    | .ltr r x y => if L.contains r then [x, y] else []
    | .orr r x y => if L.contains r then [x, y] else []
    | _ => []

/-- Drop what speaks of dead symbols (comparison chains closed three times, so solc 0.4's
`ISZERO ISZERO ISZERO (GT b a)` guard keeps its comparison, amendment A12; `refine` learns in four
rounds, and a fact dropped here is only forgotten). -/
def WSt.prune (σ : WSt) : WSt :=
  let L := closeLive σ.facts (closeLive σ.facts (closeLive σ.facts σ.liveSyms))
  { σ with
    facts := σ.facts.filter fun f => f.syms.all (L.contains ·)
    prov := σ.prov.filter fun p => L.contains p.1
    eqs := σ.eqs.filter fun e => L.contains e.1 }

def WSt.constOf (σ : WSt) (s : Nat) : Option Nat :=
  match σ.provOf s with
  | .const c => some c.toNat
  | _ => none

/-- Forget the memory words overlapping `[lo, hi)`. -/
def memKillS (m : List (Nat × Nat)) (lo hi : Nat) : List (Nat × Nat) :=
  m.filter fun p => decide (p.1 + 32 ≤ lo) || decide (hi ≤ p.1)

/-- Keep only the memory words that end at or below `b` (a write whose window starts at or
above `b`; memory is indexed by naturals, so the window cannot wrap below). -/
def memBelow (m : List (Nat × Nat)) (b : Nat) : List (Nat × Nat) :=
  m.filter fun p => decide (p.1 + 32 ≤ b)

/-- The memory effect of `n` over its input symbols. -/
def memEff (σ : WSt) (n : Ninst) : List (Nat × Nat) :=
  let lo := FreePtr.lo σ.facts
  match n, σ.kv with
  | .reg .mstore, a :: v :: _ =>
    match σ.constOf a with
    | some o => (o, v) :: memKillS σ.mem o (o + 32)
    | none => memBelow σ.mem (lo a)
  | .reg .mstore8, a :: _ :: _ =>
    match σ.constOf a with
    | some o => memKillS σ.mem o (o + 1)
    | none => memBelow σ.mem (lo a)
  | .reg .calldatacopy, d :: _ => memBelow σ.mem (lo d)
  | .reg .codecopy, d :: _ => memBelow σ.mem (lo d)
  | .reg .returndatacopy, d :: _ => memBelow σ.mem (lo d)
  | .reg .mcopy, d :: _ => memBelow σ.mem (lo d)
  | .reg .extcodecopy, _ :: d :: _ => memBelow σ.mem (lo d)
  | .exec .call, _ :: _ :: _ :: _ :: _ :: o :: _ => memBelow σ.mem (lo o)
  | .exec .callcode, _ :: _ :: _ :: _ :: _ :: o :: _ => memBelow σ.mem (lo o)
  | .exec .delegatecall, _ :: _ :: _ :: _ :: o :: _ => memBelow σ.mem (lo o)
  | .exec .staticcall, _ :: _ :: _ :: _ :: o :: _ => memBelow σ.mem (lo o)
  | n, _ => if ninstMemKeeps n then σ.mem else []

/-- The term of the fresh result `r` of `n` over the input symbols (`top`: no entry). -/
def provEff (σ : WSt) (n : Ninst) : Term :=
  match n, σ.kv with
  | .reg .caller, _ => .caller
  | .reg .address, _ => .self
  | .reg .calldataload, x :: _ => mkCd (σ.provOf x)
  | .reg .not, x :: _ =>
    match σ.provOf x with
    | .const c => .const (~~~ c)
    | _ => .top
  | .reg .keccak256, o :: l :: _ =>
    match σ.constOf o, σ.constOf l with
    | some o, some 64 =>
      match σ.mem.lookup o, σ.mem.lookup (o + 32) with
      | some s0, some s1 => mkKecc (σ.provOf s0) (σ.provOf s1)
      | _, _ => .top
    | some o, some 32 =>
      match σ.mem.lookup o with
      | some s0 => mkKecc1 (σ.provOf s0)
      | none => .top
    | _, _ => .top
  | .reg r, x :: y :: _ =>
    match Op2.ofRinst r with
    | some o => mkOp2 o (σ.provOf x) (σ.provOf y)
    | none => .top
  | _, _ => .top

/-- The symbol of the current value at an `SLOAD`'s slot, if the state has one. -/
def sloadName (σ : WSt) (n : Ninst) : Option Nat :=
  match n, σ.kv with
  | .reg .sload, k :: _ =>
    let T := σ.provOf k
    if T.known then (σ.cur.find? (·.2 == T)).map Prod.fst else none
  | _, _ => none

/-- The observed site of an `SSTORE(k, v)`. -/
def siteOf (σ : WSt) (k v : Nat) : Site :=
  let T := σ.provOf k
  ⟨T, σ.guards, T.known && (σ.ub.contains (v, T) || σ.cur.contains (v, T) ||
    σ.cur.any (fun p => p.2 == T && FreePtr.entails σ.facts (.le v p.1)))⟩

/-- An instruction that may write the executing account's storage (any call but `STATICCALL`
may re-enter it). -/
def _root_.Jaune.Ninst.writesStor : Ninst → Bool
  | .reg .sstore => true
  | .exec x => x != .staticcall
  | _ => false

/-- One non-jump instruction on the abstract state, under the current function's summary `R`;
`none` rejects (an `SSTORE` no listed site covers, or a storage write in a keeping function). -/
def wstep (R : WRet) (n : Ninst) (σ : WSt) : Option WSt :=
  match n with
  | .push bs _ =>
    let r := σ.fresh
    let c := Bytes.toB256 bs
    some (WSt.prune { σ with
      kv := (r :: σ.kv)
      prov := ((r, .const c) :: σ.prov)
      facts := (.bnd r c.toNat c.toNat :: σ.facts) })
  | n => do
    let out ← ninstTransfer n (indexPattern σ.kv.length)
    guard (out.count none ≤ 1)
    guard (!(R.keeps && n.writesStor))
    match n, σ.kv with
    | .reg .sstore, k :: v :: _ => guard (R.sites.any (·.covers (siteOf σ k v)))
    | _, _ => pure ()
    let r := σ.fresh
    let r' := (sloadName σ n).getD r
    let kv' ← out.mapM (fun l => match l with
      | none => some r'
      | some j => σ.kv[j.toNat]?)
    let t := provEff σ n
    -- a symbolic `SUB` below its minuend
    let subLe : List Fact := match n, σ.kv with
      | .reg .sub, x :: y :: _ => if FreePtr.entails σ.facts (.le y x) then [.le r x] else []
      | _, _ => []
    let subUb : List (Nat × Term) := match n, σ.kv with
      | .reg .sub, x :: y :: _ =>
        if FreePtr.entails σ.facts (.le y x) then
          (σ.cur ++ σ.ub).filterMap fun p => if p.1 = x then some (r, p.2) else none
        else []
      | _, _ => []
    let newCur : List (Nat × Term) := match n, σ.kv with
      | .reg .sload, k :: _ =>
        if (σ.provOf k).known && r' = r then [(r, σ.provOf k)] else []
      | _, _ => []
    let keepStor := !n.writesStor
    some (WSt.prune {
      kv := kv', args := σ.args,
      facts := subLe ++ FreePtr.opFacts σ.facts n σ.kv r ++ σ.facts,
      prov := (if t.known && r' = r then [(r, t)] else []) ++ σ.prov,
      mem := memEff σ n,
      cur := newCur ++ (if keepStor then σ.cur else []),
      ub := subUb ++ (if keepStor then σ.ub else []),
      eqs := (match n, σ.kv with
        | .reg .eq, x :: y :: _ => [(r, σ.provOf x, σ.provOf y)]
        | _, _ => []) ++ σ.eqs,
      guards := σ.guards })

/-- The guard a nonzero `EQ` result over words with terms `t`, `u` gives. -/
def eqGuard (t u : Term) : Option (Term × B256) :=
  match t, u with
  | t, .const k => if t.known then some (t, k) else none
  | .const k, t => if t.known then some (t, k) else none
  | _, _ => none

/-- A `JUMPI` on condition symbol `c`, on its zero (`zero = true`) or nonzero arm: the free-pointer
checker's three learning rounds, then a fourth from every zero and nonzero bound they hold
(amendment A12). -/
def refine (σ : WSt) (c : Nat) (kv : List Nat) (zero : Bool) : WSt :=
  let g := if zero then [] else
    σ.eqs.filterMap fun e => if e.1 = c then eqGuard e.2.1 e.2.2 else none
  let fs := FreePtr.refineFacts σ.facts c zero
  WSt.prune { σ with
    kv := kv
    facts := FreePtr.learn1 fs (FreePtr.zeros fs) (FreePtr.ones fs) ++ fs
    guards := g ++ σ.guards }

def popped (σ : WSt) (kv : List Nat) : WSt := WSt.prune { σ with kv := kv }

/-- The incoming symbol an annotation symbol names (frame words, then entry words). -/
def symMap (A σ : WSt) (a : Nat) : Nat := (((A.kv ++ A.args).zip (σ.kv ++ σ.args)).lookup a).getD 0

/-- The incoming state satisfies the annotation (a goto, a loop head, a join).  The annotation's
entry words may be a prefix of the incoming ones: a tail shared by functions of different arities
(amendment A9, C1). -/
def compat (σ A : WSt) : Bool :=
  let m := symMap A σ
  let own := A.kv ++ A.args
  σ.kv.length == A.kv.length && decide (A.args.length ≤ σ.args.length) &&
    ((A.kv ++ A.args).zip (σ.kv ++ σ.args)).all (fun p => m p.1 == p.2) &&
    A.syms.all (own.contains ·) &&
    A.facts.all (fun f => FreePtr.entails σ.facts (f.rename m)) &&
    A.prov.all (fun p => !p.2.known || σ.provOf (m p.1) == p.2) &&
    A.mem.all (fun p => σ.mem.contains (p.1, m p.2)) &&
    A.cur.all (fun p => σ.cur.contains (m p.1, p.2)) &&
    A.ub.all (fun p => σ.ub.contains (m p.1, p.2) || σ.cur.contains (m p.1, p.2)) &&
    A.eqs.all (fun e => σ.eqs.contains (m e.1, e.2.1, e.2.2)) &&
    A.guards.all (σ.guards.contains ·)

/-- A callee site instantiated at a call: the caller's terms for its entry words, and the
caller's guards. -/
def instSite (pa : List Term) (gs : List (Term × B256)) (s : Site) : Site :=
  ⟨s.slot.subst pa,
    ((s.guards.map fun g => (g.1.subst pa, g.2)).filter fun g => g.1.known) ++ gs, s.nonInc⟩

/-- The state a call continuation resumes in: the callee's returned words, fresh, with their
instantiated terms and order facts, above the caller's words below the callee's frame. -/
def resume (σ : WSt) (cw below : List Nat) (R : WRet) (rets : Nat) : WSt :=
  let base := σ.fresh
  let pa := cw.map σ.provOf
  let rs := (List.range rets).map (base + ·)
  let prov := (List.range rets).filterMap fun j =>
    let t := (R.prov.getD j .top).subst pa
    if t.known then some (base + j, t) else none
  let les := R.les.filterMap fun p => cw[p.2]?.map fun s => Fact.le (base + p.1) s
  let ubs := if R.keeps then
      R.les.flatMap fun p => match cw[p.2]? with
        | some s => (σ.cur ++ σ.ub).filterMap fun q => if q.1 = s then some (base + p.1, q.2) else none
        | none => []
    else []
  WSt.prune {
    kv := (rs ++ below)
    args := σ.args
    facts := (les ++ σ.facts)
    prov := (prov ++ σ.prov)
    mem := []
    cur := (if R.keeps then σ.cur else [])
    ub := (ubs ++ (if R.keeps then σ.ub else []))
    eqs := σ.eqs
    guards := σ.guards }

/-- The `.ret` check: the returned words meet the summary. -/
def retOk (σ : WSt) (kv : List Nat) (R : WRet) : Bool :=
  kv.length == R.prov.length &&
    (R.prov.zip kv).all (fun p => !p.1.known || σ.provOf p.2 == p.1) &&
    R.les.all fun p => match kv[p.1]?, σ.args[p.2]? with
      | some s, some a => FreePtr.entails σ.facts (.le s a)
      | _, _ => false

/-- The term names no entry word. -/
def Term.argFree : Term → Bool
  | .arg _ => false
  | .cd t => t.argFree
  | .op2 _ a b => a.argFree && b.argFree
  | .kecc a b => a.argFree && b.argFree
  | .kecc1 t => t.argFree
  | _ => true

/-- The summary names no entry word: it reads the same in every environment of the frame. -/
def WRet.argFree (R : WRet) : Bool :=
  R.les.isEmpty && R.prov.all Term.argFree &&
    R.sites.all fun s => s.slot.argFree && s.guards.all fun g => g.1.argFree

/-- A goto target's summary `A` is below the jumper's `R`: the same returned words and order facts,
keeping when `R` keeps, and each site covered (amendment A9, C3). -/
def retLe (A R : WRet) : Bool :=
  A.prov == R.prov && A.les == R.les && (!R.keeps || A.keeps) &&
    A.sites.all fun s => R.sites.any (·.covers s)

/-- A goto's state check: `compat`, or a tail call into a callee entry (its parameter state)
whose summary names no entry word, with exactly the callee's frame on the stack (amendment A9,
C2). -/
def gotoOk (e : Entry) (σ : WSt) (A : WAnn) : Bool :=
  compat σ A.entry ||
    (A.ret.argFree && A.entry == WSt.param e.frame.length && σ.kv.length == e.frame.length)

/-- The write-site walk over one tree, under the current function's summary `R`. -/
def wsNode (es : List Entry) (ann : List WAnn) (R : WRet) :
    List AVal → WSt → SFunc → Bool
  | a, σ, .next n f =>
    match absNinst n a, wstep R n σ with
    | some a', some σ' => wsNode es ann R a' σ' f
    | _, _ => false
  | _, _, .last _ => true
  | a, σ, .dest f => wsNode es ann R a σ f
  | a, σ, .branch f g =>
    match a, σ.kv with
    | _ :: _ :: a', _ :: c :: kv =>
      wsNode es ann R a' (refine σ c kv true) f && wsNode es ann R a' (refine σ c kv false) g
    | _, _ => false
  | a, σ, .branchTo f k =>
    match a, σ.kv, es[k]?, ann[k]? with
    | _ :: _ :: a', _ :: c :: kv, some e, some A =>
      gotoCompat a' e.frame &&
        wsNode es ann R a' (refine σ c kv true) f && gotoOk e (refine σ c kv false) A &&
        retLe A.ret R
    | _, _, _, _ => false
  | a, σ, .jump k =>
    match a, σ.kv, es[k]?, ann[k]? with
    | _ :: a', _ :: kv, some e, some A =>
      gotoCompat a' e.frame && gotoOk e (popped σ kv) A && retLe A.ret R
    | _, _, _, _ => false
  | a, σ, .callNext k f =>
    match a, σ.kv, es[k]?, ann[k]? with
    | .const _ :: a', _ :: kv, some e, some A =>
      let cw := kv.take e.frame.length
      decide (e.frame.length ≤ kv.length) &&
      A.entry == WSt.param e.frame.length && decide (A.ret.prov.length = e.rets) &&
        (!R.keeps || A.ret.keeps) &&
        A.ret.sites.all (fun s => R.sites.any (·.covers (instSite (cw.map σ.provOf) σ.guards s))) &&
        match e.frame.findIdx? (· == .ret) with
        | some i =>
          match a'[i]? with
          | some (.const _) =>
            wsNode es ann R (List.replicate e.rets .unk ++ a'.drop e.frame.length)
              (resume σ cw (kv.drop e.frame.length) A.ret e.rets) f
          | _ => false
        | none => true
    | _, _, _, _ => false
  | a, σ, .ret =>
    match a, σ.kv with
    | .ret :: _, _ :: kv => retOk σ kv R
    | _, _ => false
  | _, _, .pcAt _ _ => false
  | _, _, .undefined => true

/-- The write-site check of a whole certificate. -/
def wsCert (c : Cert) (ann : List WAnn) : Bool :=
  ann.length == c.length && (ann[0]?.map WAnn.entry) == some WSt.init &&
    (c.zip ann).all fun p => wsNode c.entries ann p.2.ret p.1.1.frame p.2.entry p.1.2

/-- The frame's write sites: entry `0`'s summary (closed terms: the root has no entry words). -/
def wsRoot (ann : List WAnn) : List Site := (ann[0]?.map (·.ret.sites)).getD []

/-- Tiny tree for `SSTORE(SLOAD(0), 1)`: the key is an `SLOAD` result (`top`), the value `1`. -/
def exTopStore : SFunc :=
  .next (.push [1] (by decide))
    (.next (.push [0] (by decide))
      (.next (.reg .sload)
        (.next (.reg .sstore) (.last .stop))))

/-- The `top` slot covers the `SLOAD`-keyed write; the empty list covers nothing. -/
def Rtop : WRet := ⟨[], [], false, [⟨.top, [], false⟩]⟩
def Rnothing : WRet := ⟨[], [], false, []⟩

example : wsNode [] [] Rtop [] WSt.init exTopStore = true &&
    wsNode [] [] Rnothing [] WSt.init exTopStore = false := by decide

/-- Tiny tree for `SSTORE(keccak(caller, 3), 1)`: the two-word hash of `caller` and `3`. -/
def exCallerStore : SFunc :=
  .next (.push [1] (by decide))
    (.next (.reg .caller)
      (.next (.push [0] (by decide))
        (.next (.reg .mstore)
          (.next (.push [3] (by decide))
            (.next (.push [32] (by decide))
              (.next (.reg .mstore)
                (.next (.push [64] (by decide))
                  (.next (.push [0] (by decide))
                    (.next (.reg .keccak256)
                      (.next (.reg .sstore) (.last .stop)))))))))))

/-- The caller-keyed slot covers the write; a calldata-keyed claim does not. -/
def Rcaller : WRet :=
  ⟨[], [], false, [⟨.kecc .caller (.const (Bytes.toB256 [3])), [], false⟩]⟩
def Rcdkey : WRet :=
  ⟨[], [], false, [⟨.kecc (.cd (.const (Bytes.toB256 [0]))) (.const (Bytes.toB256 [3])), [], false⟩]⟩

example : wsNode [] [] Rcaller [] WSt.init exCallerStore = true &&
    wsNode [] [] Rcdkey [] WSt.init exCallerStore = false := by decide

end Blanc.Lift.WriteSite
