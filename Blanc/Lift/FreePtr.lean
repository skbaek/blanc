import Blanc.Lift.Check
import Blanc.Lift.MemPotential

/-! ## F1  `Blanc/Lift/FreePtr.lean` (checker; contract-neutral) -/

namespace Blanc.Lift.FreePtr

open Jaune AbstractStackSafety

/-- A fact about symbols (meaning: `FreePtr.Fact.Holds`, F3). -/
inductive Fact : Type
  /-- `lo ≤ s ≤ hi` as natural numbers. -/
  | bnd (s lo hi : Nat)
  /-- `s ≤ t`. -/
  | le (s t : Nat)
  /-- `s < t`. -/
  | lt (s t : Nat)
  /-- `r = LT(x, y)` (Jaune's `ltCheck`, top `x`). -/
  | ltr (r x y : Nat)
  /-- `r = ISZERO(s)`. -/
  | isz (r s : Nat)
  /-- `r = OR(x, y)`. -/
  | orr (r x y : Nat)
deriving DecidableEq

def Fact.syms : Fact → List Nat
  | .bnd s _ _ => [s]
  | .le s t => [s, t]
  | .lt s t => [s, t]
  | .ltr r x y => [r, x, y]
  | .isz r s => [r, s]
  | .orr r x y => [r, x, y]

def Fact.rename (m : Nat → Nat) : Fact → Fact
  | .bnd s lo hi => .bnd (m s) lo hi
  | .le s t => .le (m s) (m t)
  | .lt s t => .lt (m s) (m t)
  | .ltr r x y => .ltr (m r) (m x) (m y)
  | .isz r s => .isz (m r) (m s)
  | .orr r x y => .orr (m r) (m x) (m y)

/-- An abstract frame state: a symbol per frame word (top first), facts, and the symbol of the
free-pointer word `memWord 0x40` (`none`: not known, before the prologue or after a write the
checker cannot place). -/
structure FSt : Type where
  kv : List Nat
  facts : List Fact
  fp : Option Nat
deriving DecidableEq

/-- Entry `k`'s annotation: the state it is entered in, and its function's return summary
(`ret.kv` is the returned words; loop heads share their function's summary). -/
structure Ann : Type where
  entry : FSt
  ret : FSt
deriving DecidableEq

def FSt.init : FSt := ⟨[], [], none⟩

def maxW : Nat := 2 ^ 256 - 1

/-- The free-pointer bound every read must meet. -/
def fpLo : Nat := 0x80
def fpCap : Nat := 2 ^ 256 - 2 ^ 32

def bndOf (fs : List Fact) (s : Nat) : Nat × Nat :=
  fs.foldl (fun p f => match f with
    | .bnd s' lo hi => if s' = s then (max p.1 lo, min p.2 hi) else p
    | _ => p) (0, maxW)

/-- `bndOf`, refined once through the order facts. -/
def bnd2 (fs : List Fact) (s : Nat) : Nat × Nat :=
  fs.foldl (fun p f => match f with
    | .lt a b =>
      if a = s then (p.1, min p.2 ((bndOf fs b).2 - 1))
      else if b = s then (max p.1 ((bndOf fs a).1 + 1), p.2) else p
    | .le a b =>
      if a = s then (p.1, min p.2 (bndOf fs b).2)
      else if b = s then (max p.1 (bndOf fs a).1, p.2) else p
    | _ => p) (bndOf fs s)

def lo (fs : List Fact) (s : Nat) : Nat := (bnd2 fs s).1
def hi (fs : List Fact) (s : Nat) : Nat := (bnd2 fs s).2

def entails (fs : List Fact) : Fact → Bool
  | .bnd s l h => decide (l ≤ lo fs s) && decide (hi fs s ≤ h)
  | .lt s t => fs.contains (.lt s t) || decide (hi fs s < lo fs t)
  | .le s t => fs.contains (.le s t) || fs.contains (.lt s t) || decide (hi fs s ≤ lo fs t)
  | f => fs.contains f

def constOf (fs : List Fact) (s : Nat) : Option Nat :=
  if lo fs s = hi fs s then some (lo fs s) else none

/-- The symbol is a good free-pointer value. -/
def good (fs : List Fact) (s : Nat) : Bool := decide (fpLo ≤ lo fs s) && decide (hi fs s ≤ fpCap)

/-- A write of `len` bytes (at most `lenHi`) at symbol `a` misses the free-pointer word. -/
def apartW (fs : List Fact) (a lenHi : Nat) : Bool :=
  decide (hi fs a + lenHi ≤ 0x40) || decide (0x60 ≤ lo fs a)

/-- An `MLOAD` at symbol `a` cannot read the free-pointer word's offset. -/
def not64 (fs : List Fact) (a : Nat) : Bool := decide (64 < lo fs a) || decide (hi fs a < 64)

def freshSym (kv : List Nat) (fs : List Fact) (fp : Option Nat) : Nat :=
  (kv ++ fp.toList ++ fs.flatMap Fact.syms).foldr max 0 + 1

def live (kv : List Nat) (fp : Option Nat) (f : Fact) : Bool :=
  f.syms.all fun s => kv.contains s || fp == some s

/-- Keep the facts live in `kv`/`fp`, closed twice through comparison results
(decision `ns-pf1-accept`): a fact about a comparison result (`isz`, `ltr`, `orr`)
stays live while the compared symbols are live, even after the result itself is
consumed. The second round lets symbols named by first-round comparison facts
keep further comparison facts. -/
def closeLive (kv : List Nat) (fp : Option Nat) (fs : List Fact) : List Fact :=
  let alive0 : Nat → Bool := fun s => kv.contains s || fp == some s
  let live1 : Fact → Bool
    | .isz _ s => alive0 s
    | .ltr _ x y => alive0 x && alive0 y
    | .orr _ x y => alive0 x && alive0 y
    | f => f.syms.all alive0
  let k1 := fs.filter live1
  let alive1 : Nat → Bool := fun s => alive0 s || k1.any (fun f => f.syms.contains s)
  let live2 : Fact → Bool
    | .isz _ s => alive1 s
    | .ltr _ x y => alive1 x && alive1 y
    | .orr _ x y => alive1 x && alive1 y
    | f => f.syms.all alive1
  fs.filter live2

/-- The facts about the fresh result `r` of `n` over the input symbols `xs` (top first). -/
def opFacts (fs : List Fact) (n : Ninst) (xs : List Nat) (r : Nat) : List Fact :=
  match n, xs with
  | .reg .add, x :: y :: _ =>
    if hi fs x + hi fs y ≤ maxW then
      [.bnd r (lo fs x + lo fs y) (hi fs x + hi fs y), .le x r, .le y r]
    else []
  | .reg .sub, x :: y :: _ =>
    if hi fs y ≤ lo fs x then [.bnd r (lo fs x - hi fs y) (hi fs x - lo fs y), .le r x] else []
  | .reg .mul, x :: y :: _ =>
    if hi fs x * hi fs y ≤ maxW then [.bnd r (lo fs x * lo fs y) (hi fs x * hi fs y)] else []
  | .reg .div, x :: y :: _ =>
    if 1 ≤ lo fs y then [.bnd r (lo fs x / hi fs y) (hi fs x / lo fs y)] else [.bnd r 0 (hi fs x)]
  | .reg .and, x :: y :: _ => [.bnd r 0 (min (hi fs x) (hi fs y))]
  | .reg .or, x :: y :: _ => [.orr r x y]
  | .reg .shr, _ :: y :: _ => [.bnd r 0 (hi fs y)]
  | .reg .lt, x :: y :: _ => [.ltr r x y, .bnd r 0 1]
  | .reg .gt, x :: y :: _ => [.ltr r y x, .bnd r 0 1]
  | .reg .iszero, x :: _ => [.isz r x, .bnd r 0 1]
  | .reg .eq, _ => [.bnd r 0 1]
  | .reg .msize, _ => [.bnd r 0 memCap]
  | _, _ => []

/-- The bound a touched window `[a, a + len)` gives after the step (memory potential, F2):
`a + len ≤ memCap`, also for every symbol below `a` by an `le` fact. -/
def touched (fs : List Fact) (a : Nat) (len : Nat) : List Fact :=
  (a :: (fs.filterMap fun f => match f with
    | .le t a' => if a' = a then some t else none
    | _ => none)).map fun t => .bnd t 0 (memCap - len)

/-- The memory effect of `n` over its input symbols `xs`: the new free-pointer symbol (the
result `r` if `n` is the free-pointer `MLOAD`), the potential facts; `none` rejects (a read
that may hit offset `0x40` while the pointer is not known to be good). -/
def memEff (fs : List Fact) (fp : Option Nat) (n : Ninst) (xs : List Nat) :
    Option (Option Nat × List Fact) :=
  match n, xs with
  | .reg .mload, a :: _ =>
    if not64 fs a then some (fp, touched fs a 32)
    else match fp with
      | some s => if good fs s then some (fp, touched fs a 32) else none
      | none => none
  | .reg .mstore, a :: v :: _ =>
    if constOf fs a = some 64 then some (if good fs v then some v else none, touched fs a 32)
    else some (if apartW fs a 32 then fp else none, touched fs a 32)
  | .reg .mstore8, a :: _ :: _ => some (if apartW fs a 1 then fp else none, touched fs a 1)
  | .reg .calldatacopy, d :: _ :: l :: _ =>
    some (if hi fs l = 0 || apartW fs d (hi fs l) then fp else none,
      if 1 ≤ lo fs l then touched fs d (lo fs l) else [])
  | .reg .codecopy, d :: _ :: l :: _ =>
    some (if hi fs l = 0 || apartW fs d (hi fs l) then fp else none,
      if 1 ≤ lo fs l then touched fs d (lo fs l) else [])
  | .reg .returndatacopy, d :: _ :: l :: _ =>
    some (if hi fs l = 0 || apartW fs d (hi fs l) then fp else none,
      if 1 ≤ lo fs l then touched fs d (lo fs l) else [])
  | .reg .mcopy, d :: _ :: l :: _ =>
    some (if hi fs l = 0 || apartW fs d (hi fs l) then fp else none,
      if 1 ≤ lo fs l then touched fs d (lo fs l) else [])
  | .reg .extcodecopy, _ :: d :: _ :: l :: _ =>
    some (if hi fs l = 0 || apartW fs d (hi fs l) then fp else none,
      if 1 ≤ lo fs l then touched fs d (lo fs l) else [])
  | .exec .call, _ :: _ :: _ :: _ :: _ :: o :: l :: _ =>
    some (if hi fs l = 0 || apartW fs o (hi fs l) then fp else none, [])
  | .exec .callcode, _ :: _ :: _ :: _ :: _ :: o :: l :: _ =>
    some (if hi fs l = 0 || apartW fs o (hi fs l) then fp else none, [])
  | .exec .delegatecall, _ :: _ :: _ :: _ :: o :: l :: _ =>
    some (if hi fs l = 0 || apartW fs o (hi fs l) then fp else none, [])
  | .exec .staticcall, _ :: _ :: _ :: _ :: o :: l :: _ =>
    some (if hi fs l = 0 || apartW fs o (hi fs l) then fp else none, [])
  | .reg .mload, [] => none
  | _, _ => some (fp, [])

/-- One non-jump instruction on the abstract state; `none` rejects. -/
def fstep (n : Ninst) (σ : FSt) : Option FSt :=
  match n with
  | .push bs _ =>
    let r := freshSym σ.kv σ.facts σ.fp
    let c := (Bytes.toB256 bs).toNat
    some ⟨r :: σ.kv, .bnd r c c :: σ.facts, σ.fp⟩
  | n => do
    let out ← ninstTransfer n (indexPattern σ.kv.length)
    guard (out.count none ≤ 1)
    let r := freshSym σ.kv σ.facts σ.fp
    let (fp', gas) ← memEff σ.facts σ.fp n σ.kv
    -- the free-pointer `MLOAD` names its result by the pointer's own symbol
    let r' := match n, σ.kv with
      | .reg .mload, a :: _ => if constOf σ.facts a = some 64 then fp'.getD r else r
      | _, _ => r
    let kv' ← out.mapM (fun l => match l with
      | none => some r'
      | some j => σ.kv[j.toNat]?)
    some ⟨kv', closeLive kv' fp' (opFacts σ.facts n σ.kv r ++ gas ++ σ.facts), fp'⟩

/-- The facts a `JUMPI` on condition symbol `c` learns on its zero / nonzero arm (two rounds
through `isz`, `ltr`, `orr`). -/
def learn1 (fs : List Fact) (z : List Nat) (nz : List Nat) : List Fact :=
  fs.flatMap fun f => match f with
    | .isz r s => if z.contains r then [.bnd s 1 maxW] else if nz.contains r then [.bnd s 0 0]
        else []
    | .ltr r x y => if z.contains r then [.le y x] else if nz.contains r then [.lt x y] else []
    | .orr r x y => if z.contains r then [.bnd x 0 0, .bnd y 0 0] else []
    | _ => []

def zeros (fs : List Fact) : List Nat :=
  fs.filterMap fun f => match f with
    | .bnd s _ 0 => some s
    | _ => none

def refineFacts (fs : List Fact) (c : Nat) (zero : Bool) : List Fact :=
  let f1 := (if zero then [Fact.bnd c 0 0] else [Fact.bnd c 1 maxW]) ++ fs
  let r1 := learn1 f1 (if zero then [c] else []) (if zero then [] else [c])
  let f2 := r1 ++ f1
  let r2 := learn1 f2 (zeros r1) ((r1.filterMap fun f => match f with
    | .bnd s 1 _ => some s
    | _ => none))
  r2 ++ f2

def refine (σ : FSt) (c : Nat) (kv : List Nat) (zero : Bool) : FSt :=
  ⟨kv, closeLive kv σ.fp (refineFacts σ.facts c zero), σ.fp⟩

def popped (σ : FSt) (kv : List Nat) : FSt := ⟨kv, closeLive kv σ.fp σ.facts, σ.fp⟩

/-- The incoming symbol an annotation symbol names. -/
def symMap (A : FSt) (σ : FSt) (a : Nat) : Nat :=
  if A.fp = some a then σ.fp.getD 0 else ((A.kv.zip σ.kv).lookup a).getD 0

/-- The incoming state satisfies the annotation. -/
def compat (σ A : FSt) : Bool :=
  σ.kv.length == A.kv.length &&
    (A.kv.zip σ.kv).all (fun p => symMap A σ p.1 == p.2) &&
    (match A.fp with
     | none => true
     | some a => σ.fp.isSome && (A.kv.all fun b => b != a)) &&
    A.facts.all (fun f => entails σ.facts (f.rename (symMap A σ)))

/-- The state a call continuation resumes in: the callee's return summary, renamed to fresh
symbols above the caller's, over the caller's words below the callee's frame. -/
def resume (σ : FSt) (below : List Nat) (R : FSt) : FSt :=
  let base := freshSym σ.kv σ.facts σ.fp
  let m := fun s => base + s
  let kv := R.kv.map m ++ below
  let fp := R.fp.map m
  ⟨kv, closeLive kv fp (R.facts.map (Fact.rename m) ++ σ.facts), fp⟩

/-- The free-pointer walk over one tree, under the current function's return summary `R`. -/
def fpNode (es : List Entry) (ann : List Ann) (R : FSt) :
    List AVal → FSt → SFunc → Bool
  | a, σ, .next n f =>
    match absNinst n a, fstep n σ with
    | some a', some σ' => fpNode es ann R a' σ' f
    | _, _ => false
  | _, _, .last _ => true
  | a, σ, .dest f => fpNode es ann R a σ f
  | a, σ, .branch f g =>
    match a, σ.kv with
    | _ :: _ :: a', _ :: c :: kv =>
      fpNode es ann R a' (refine σ c kv true) f && fpNode es ann R a' (refine σ c kv false) g
    | _, _ => false
  | a, σ, .branchTo f k =>
    match a, σ.kv, ann[k]? with
    | _ :: _ :: a', _ :: c :: kv, some A =>
      fpNode es ann R a' (refine σ c kv true) f && compat (refine σ c kv false) A.entry &&
        A.ret == R
    | _, _, _ => false
  | _, σ, .jump k =>
    match σ.kv, ann[k]? with
    | _ :: kv, some A => compat (popped σ kv) A.entry && A.ret == R
    | _, _ => false
  | a, σ, .callNext k f =>
    match a, σ.kv, es[k]?, ann[k]? with
    | .const _ :: a', _ :: kv, some e, some A =>
      compat (popped σ (kv.take e.frame.length)) A.entry &&
        decide (A.ret.kv.length = e.rets) &&
        match e.frame.findIdx? (· == .ret) with
        | some i =>
          match a'[i]? with
          | some (.const _) =>
            fpNode es ann R (List.replicate e.rets .unk ++ a'.drop e.frame.length)
              (resume σ (kv.drop e.frame.length) A.ret) f
          | _ => false
        | none => true
    | _, _, _, _ => false
  | _, σ, .ret =>
    match σ.kv with
    | _ :: kv => compat (popped σ kv) R
    | [] => false
  | _, _, .pcAt _ _ => false
  | _, _, .undefined => true

/-- The free-pointer check of a whole certificate. -/
def fpCert (c : Cert) (ann : List Ann) : Bool :=
  ann.length == c.length && (ann[0]?.map Ann.entry) == some FSt.init &&
    (c.zip ann).all fun p => fpNode c.entries ann p.2.ret p.1.1.frame p.2.entry p.1.2

/-- Toy store: `PUSH 0x80; PUSH 0x40; MSTORE` (value `0x80` at the free-pointer
word), followed by `PUSH 0x40; MLOAD`. -/
def toyStore : SFunc :=
  .next (.push [0x80] (by decide))
    (.next (.push [0x40] (by decide))
      (.next (.reg .mstore)
        (.next (.push [0x40] (by decide))
          (.next (.reg .mload) (.last .stop)))))

/-- Toy store writing `0x20` instead: below the free-pointer bound. -/
def toyStoreBad : SFunc :=
  .next (.push [0x20] (by decide))
    (.next (.push [0x40] (by decide))
      (.next (.reg .mstore)
        (.next (.push [0x40] (by decide))
          (.next (.reg .mload) (.last .stop)))))

example : fpNode [] [] FSt.init [] FSt.init toyStore = true := by decide

example : fpNode [] [] FSt.init [] FSt.init toyStoreBad = false := by decide

end Blanc.Lift.FreePtr
