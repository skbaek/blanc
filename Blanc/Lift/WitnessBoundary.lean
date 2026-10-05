import Blanc.Lift.WitnessChild

/-!
# Chunk boundaries and stage composition for a witness run

A long `Witness.wrun` is decided by the kernel as several chunks between literal
boundaries: each chunk is its own declaration, so the kernel's caches do not outlive it,
and the boundary literals are printed by an untrusted scratch evaluation that the chunk
decisions check.  This module is the literal-free scaffolding of that method, stated over
the boundaries, the interpreter's program `fs` and the frame's static machine `sta` as
parameters.  Nothing here is contract-specific.

* `Bnd`, `obsB`, `cfgOf`, `obsD`, `obsDOk`: a boundary (the machine, the node, the pending
  returns, the four shadows, the refund counter, the output and return data, the error) and
  a chunk's end decided against it.  `obsD` compares the machine and the shadows by
  `decide` (so the kernel evaluates them) and the node, the pending returns and the account
  shadow as terms; comparing the lazily computed machine to a literal as a term instead
  exhausts the kernel's recursion once the world and bookkeeping are free.  A
  configuration so decided is `cfgOf` of its boundary at its own world and bookkeeping
  (`cfg_of_obsD`), so a run through a boundary is a chunk up to it followed by one from it
  over any world and bookkeeping (`obsD_chain`, `obsD_chain3`, `obsB_of_obsD`,
  `run_of_obsB`).  Every boundary also records that the set of accounts to delete is still the
  empty one a frame starts with (compared as a term), so a run through boundaries shows the
  frame deletes nothing.
* `Bnd1`, `obsD1`, `obsDOk1`, `cfgOf1`: the same with the refund counter optional (`none`:
  free), deciding the account shadow by its address, nonce and balance (`acctKey`) and
  comparing each account's storage and code as terms (`acctRest`), and the set of accounts to
  delete against the empty set when the boundary records it.  After a child's `CALL` some accounts' addresses
  are computed from stack words, and comparing such a shadow to a literal as a term
  exhausts the kernel.
* `callPairFrom`, `callPairA`, `callPairB`, `callPairFrom_stages`: a frame that makes two
  code-child calls, the first a settled child supplied as data and the second run by its own
  program (`childRun`), is decided in four stages over three boundaries; the composition is
  over variables only, so the kernel evaluates nothing outside the stages.
-/

namespace Blanc.Lift.Witness.Boundary

open Jaune Blanc.Lift Blanc.Lift.Witness

/-! ### Boundaries with the refund counter -/

/-- What `obsB` observes of a configuration: the machine, the node, the pending returns,
the storage keys, the addresses, the storage and account shadows, the refund counter, the
output, the return data and the error. -/
abbrev Bnd := Mach × SFunc × List SFunc × List (Adr × B256) × List Adr × StorShadow ×
  AcctShadow × Int × Bytes × Bytes × Option SettledHalt

/-- What a configuration shows as a boundary. -/
def obsB : Res → Option Bnd
  | .cont c => some (c.devm.mach, c.f, c.K, c.keys, c.adrs, c.stor, c.acs, c.devm.refundCounter,
      c.devm.output, c.devm.returnData, c.devm.error)
  | _ => none

/-- The configuration at boundary `x` (with no error), over a free world and free
bookkeeping; the set of accounts to delete is the empty one a frame starts with (a boundary
records it as a term, `obsD`). -/
def cfgOf : Bnd → Meta → World → Cfg
  | (mach, f, K, keys, adrs, stor, acs, rc, out, rd, _), m, w =>
    ⟨⟨mach, { { m with refundCounter := rc, output := out, returnData := rd, error := none } with
      accountsToDelete := .emptyWithCapacity }, w⟩, f, K, keys, adrs, stor, acs⟩

/-- A chunk's end decided against boundary `x`: the last component is the set of accounts to
delete, compared as a term against the empty set. -/
def obsD : Bnd → Res → Option (Bool × SFunc × List SFunc × AcctShadow × AdrSet)
  | (mach, _, _, keys, adrs, stor, _, rc, out, rd, err), .cont c =>
    some (decide (c.devm.mach.stack = mach.stack) &&
      decide (c.devm.mach.memory.data.toList = mach.memory.data.toList) &&
      decide (c.devm.mach.memory.size = mach.memory.size) &&
      decide (c.devm.mach.gasLeft = mach.gasLeft) &&
      decide (c.devm.mach.stateGas = mach.stateGas) && decide (c.keys = keys) &&
      decide (c.adrs = adrs) && decide (c.stor = stor) && decide (c.devm.refundCounter = rc) &&
      decide (c.devm.output = out) && decide (c.devm.returnData = rd) &&
      c.devm.error.isNone && err.isNone, c.f, c.K, c.acs, c.devm.accountsToDelete)
  | _, _ => none

/-- What `obsD` shows at boundary `x`. -/
def obsDOk : Bnd → Option (Bool × SFunc × List SFunc × AcctShadow × AdrSet)
  | (_, f, K, _, _, _, acs, _, _, _, _) => some (true, f, K, acs, .emptyWithCapacity)

/-- A result whose configuration (if it is one) has the empty set of accounts to delete.
Irreducible: the elaborator must not evaluate the run it is stated about. -/
@[irreducible] def AtdClean : Res → Prop
  | .cont c => c.devm.accountsToDelete = .emptyWithCapacity
  | _ => True

theorem atdClean_cont {c : Cfg} : AtdClean (.cont c) ↔ c.devm.accountsToDelete = .emptyWithCapacity := by
  unfold AtdClean; exact Iff.rfl

/-- A configuration decided at boundary `x` is `cfgOf x` at its own world and bookkeeping. -/
theorem cfg_of_obsD {c : Cfg} {x : Bnd} (h : obsD x (.cont c) = obsDOk x) :
    c = cfgOf x c.devm.meta c.devm.world := by
  rcases x with ⟨⟨s, ⟨data, size⟩, g, sg⟩, f, K, keys, adrs, stor, acs, rc, out, rd, err⟩
  rcases c with ⟨⟨⟨s', ⟨data', size'⟩, g', sg'⟩, m, w⟩, f', K', keys', adrs', stor', acs'⟩
  simp only [obsD, obsDOk, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] at h
  obtain ⟨hs, hd, hsz, hg, hsg, hk, ha, hst, hrc, ho, hrd, he, -, hf, hK, hc, hat⟩ := h
  have hd' : data' = data := Array.toList_inj.mp hd
  subst hs hd' hsz hg hsg hk ha hst hf hK hc
  rcases m with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  simp only [Devm.refundCounter, Devm.output, Devm.returnData, Devm.error,
    Option.isNone_iff_eq_none, Devm.accountsToDelete] at hrc ho hrd he hat
  subst hrc ho hrd he hat
  rfl

/-- A configuration observed as boundary `x` (which records no error) with the empty set of
accounts to delete is `cfgOf x` at its own world and bookkeeping. -/
theorem cfg_of_obsB {c : Cfg} {x : Bnd} (h : obsB (.cont c) = some x)
    (hx : x.2.2.2.2.2.2.2.2.2.2 = none) (hat : c.devm.accountsToDelete = .emptyWithCapacity) :
    c = cfgOf x c.devm.meta c.devm.world := by
  rcases x with ⟨mach, f, K, keys, adrs, stor, acs, rc, out, rd, err⟩
  cases hx
  rcases c with ⟨⟨mach', m, w⟩, f', K', keys', adrs', stor', acs'⟩
  simp only [obsB, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hm, hf, hK, hk, ha, hs, hc, hrc, ho, hrd, he⟩ := h
  subst hm hf hK hk ha hs hc
  rcases m with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  simp only [Devm.refundCounter, Devm.output, Devm.returnData, Devm.error,
    Devm.accountsToDelete] at hrc ho hrd he hat
  subst hrc ho hrd he hat
  rfl

/-- `obsB` of a boundary's configuration is the boundary (when it records no error). -/
theorem obsB_cfgOf {x : Bnd} (hx : x.2.2.2.2.2.2.2.2.2.2 = none) (m : Meta) (w : World) :
    obsB (.cont (cfgOf x m w)) = some x := by
  rcases x with ⟨mach, f, K, keys, adrs, stor, acs, rc, out, rd, err⟩
  cases hx
  rfl

/-- A run through boundary `x`: a chunk of `n` steps decided at `x`, then one of `k` steps
from `x` over any world and bookkeeping. -/
theorem obsD_chain {P : Res → Prop} {fs : List SFunc} {sta : Sevm} {n k : Nat} {c : Cfg}
    {x : Bnd} (h1 : obsD x (wrun fs sta n c) = obsDOk x)
    (h2 : ∀ m w, P (wrun fs sta k (cfgOf x m w))) : P (wrun fs sta (n + k) c) := by
  rw [wrun_add]
  generalize wrun fs sta n c = r at h1 ⊢
  rcases r with c' | _ | _
  · rw [cfg_of_obsD h1]
    exact h2 _ _
  · rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    simp only [obsD, obsDOk, reduceCtorEq] at h1
  · rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    simp only [obsD, obsDOk, reduceCtorEq] at h1

/-- Three chunks from a configuration that is `cfgOf x0` at its own world and bookkeeping,
decided at `x1`, `x2` and `x3` over any world and bookkeeping, are one chunk decided at
`x3`. -/
theorem obsD_chain3 {fs : List SFunc} {sta : Sevm} {n1 n2 n3 : Nat} {c : Cfg} {x0 x1 x2 x3 : Bnd}
    (hc : c = cfgOf x0 c.devm.meta c.devm.world)
    (h1 : ∀ m w, obsD x1 (wrun fs sta n1 (cfgOf x0 m w)) = obsDOk x1)
    (h2 : ∀ m w, obsD x2 (wrun fs sta n2 (cfgOf x1 m w)) = obsDOk x2)
    (h3 : ∀ m w, obsD x3 (wrun fs sta n3 (cfgOf x2 m w)) = obsDOk x3) :
    obsD x3 (wrun fs sta (n1 + n2 + n3) c) = obsDOk x3 := by
  rw [hc]
  exact obsD_chain (P := fun r => obsD x3 r = obsDOk x3)
    (obsD_chain (P := fun r => obsD x2 r = obsDOk x2) (h1 _ _) h2) h3

/-- A run decided at boundary `x` (which records no error) is observed as `x`, with the empty
set of accounts to delete. -/
theorem obsB_of_obsD {fs : List SFunc} {sta : Sevm} {n : Nat} {c : Cfg} {x : Bnd}
    (h : obsD x (wrun fs sta n c) = obsDOk x) (hx : x.2.2.2.2.2.2.2.2.2.2 = none) :
    obsB (wrun fs sta n c) = some x ∧ AtdClean (wrun fs sta n c) := by
  generalize wrun fs sta n c = r at h ⊢
  rcases r with c' | _ | _
  · rw [cfg_of_obsD h]
    exact ⟨obsB_cfgOf hx _ _, atdClean_cont.mpr rfl⟩
  · rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    simp only [obsD, obsDOk, reduceCtorEq] at h
  · rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    simp only [obsD, obsDOk, reduceCtorEq] at h

/-- A run observed as boundary `x` (which records no error) with the empty set of accounts to
delete, followed by `k` steps decided from `x` over any world and bookkeeping. -/
theorem run_of_obsB {P : Res → Prop} {fs : List SFunc} {sta : Sevm} {n k : Nat} {c : Cfg}
    {x : Bnd} (hA : obsB (wrun fs sta n c) = some x) (hat : AtdClean (wrun fs sta n c))
    (hx : x.2.2.2.2.2.2.2.2.2.2 = none)
    (hB : ∀ m w, P (wrun fs sta k (cfgOf x m w))) : P (wrun fs sta (n + k) c) := by
  rw [wrun_add]
  generalize wrun fs sta n c = r at hA hat ⊢
  rcases r with c' | _ | _
  · rw [cfg_of_obsB hA hx (atdClean_cont.mp hat)]
    exact hB _ _
  · simp only [obsB, reduceCtorEq] at hA
  · simp only [obsB, reduceCtorEq] at hA

/-! ### Boundaries with an optional refund counter -/

/-- A boundary: machine, node, pending returns, the four shadows, output and return data, the
refund counter when it is recorded (`none`: free), and whether it records that the set of
accounts to delete is the empty one a frame starts with (`false`: free). -/
abbrev Bnd1 := Mach × SFunc × List SFunc × List (Adr × B256) × List Adr × StorShadow ×
  AcctShadow × Bytes × Bytes × Option Int × Bool

/-- `m` with the refund counter `rc` when one is recorded. -/
def setRc : Option Int → Meta → Meta
  | none, m => m
  | some r, m => { m with refundCounter := r }

/-- `m` with the empty set of accounts to delete when the boundary records it. -/
def setAtd : Bool → Meta → Meta
  | false, m => m
  | true, m => { m with accountsToDelete := .emptyWithCapacity }

/-- The set of accounts to delete a boundary compares (the empty set when it records none). -/
def atdOf1 : Bool → AdrSet → AdrSet
  | false, _ => .emptyWithCapacity
  | true, a => a

/-- The configuration at boundary `x` (with no error), over a free world and free
bookkeeping (the refund counter included unless the boundary records it, and likewise the set
of accounts to delete). -/
def cfgOf1 : Bnd1 → Meta → World → Cfg
  | (mach, f, K, keys, adrs, stor, acs, out, rd, rc, atd), m, w =>
    ⟨⟨mach, setAtd atd (setRc rc { m with output := out, returnData := rd, error := none }), w⟩,
      f, K, keys, adrs, stor, acs⟩

/-- An account-shadow entry's address, nonce and balance: what a boundary decides. -/
def acctKey (p : Adr × Acct) : Adr × UInt64 × B256 := (p.1, p.2.nonce, p.2.bal)

/-- An account-shadow entry's storage and code: what a boundary compares as terms. -/
def acctRest (p : Adr × Acct) : Stor × ByteArray := (p.2.stor, p.2.code)

/-- `acctRest` of a boundary's literal shadow, by its own recursion: were both sides of a
boundary's comparison `List.map acctRest`, the kernel would first compare the two shadows
themselves as terms. -/
def restsOf : AcctShadow → List (Stor × ByteArray)
  | [] => []
  | p :: l => (p.2.stor, p.2.code) :: restsOf l

theorem restsOf_eq : ∀ l : AcctShadow, restsOf l = l.map acctRest
  | [] => rfl
  | _ :: l => by rw [restsOf, List.map_cons, restsOf_eq l]; rfl

theorem acs_eq_of_views : ∀ {l l' : AcctShadow}, l.map acctKey = l'.map acctKey →
    l.map acctRest = l'.map acctRest → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp only [List.map_nil, List.map_cons, List.nil_eq, reduceCtorEq] at h
  | _ :: _, [], h, _ => by simp only [List.map_cons, List.map_nil, reduceCtorEq] at h
  | (_, ⟨_, _, _, _⟩) :: _, (_, ⟨_, _, _, _⟩) :: _, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq, acctKey, acctRest, Prod.mk.injEq] at h1 h2
    obtain ⟨⟨rfl, rfl, rfl⟩, h1⟩ := h1
    obtain ⟨⟨rfl, rfl⟩, h2⟩ := h2
    rw [acs_eq_of_views h1 h2]

/-- A chunk's end decided against boundary `x`: the machine, the storage-key, address and
storage shadows, each account's address, nonce and balance, the output and the return data by
`decide`; the node, the pending returns and each account's storage and code as terms; the refund counter by `decide` when the boundary records it, and
the set of accounts to delete as a term against the empty set. -/
def obsD1 : Bnd1 → Res →
    Option (Bool × SFunc × List SFunc × List (Stor × ByteArray) × AdrSet)
  | (mach, _, _, keys, adrs, stor, acs, out, rd, rc, atd), .cont c =>
    some (decide (c.devm.mach.stack = mach.stack) &&
      decide (c.devm.mach.memory.data.toList = mach.memory.data.toList) &&
      decide (c.devm.mach.memory.size = mach.memory.size) &&
      decide (c.devm.mach.gasLeft = mach.gasLeft) &&
      decide (c.devm.mach.stateGas = mach.stateGas) && decide (c.keys = keys) &&
      decide (c.adrs = adrs) && decide (c.stor = stor) &&
      decide (c.acs.map acctKey = acs.map acctKey) && decide (c.devm.output = out) &&
      decide (c.devm.returnData = rd) && c.devm.error.isNone &&
      (match rc with | none => true | some r => decide (c.devm.refundCounter = r)),
      c.f, c.K, c.acs.map acctRest, atdOf1 atd c.devm.accountsToDelete)
  | _, _ => none

/-- What `obsD1` shows at boundary `x`. -/
def obsDOk1 : Bnd1 → Option (Bool × SFunc × List SFunc × List (Stor × ByteArray) × AdrSet)
  | (_, f, K, _, _, _, acs, _, _, _, _) => some (true, f, K, restsOf acs, .emptyWithCapacity)

/-- A configuration decided at boundary `x` is `cfgOf1 x` at its own world and bookkeeping. -/
theorem cfg_of_obsD1 {c : Cfg} {x : Bnd1} (h : obsD1 x (.cont c) = obsDOk1 x) :
    c = cfgOf1 x c.devm.meta c.devm.world := by
  rcases x with ⟨⟨s, ⟨data, size⟩, g, sg⟩, f, K, keys, adrs, stor, acs, out, rd, rc, atd⟩
  rcases c with ⟨⟨⟨s', ⟨data', size'⟩, g', sg'⟩, m, w⟩, f', K', keys', adrs', stor', acs'⟩
  simp only [obsD1, obsDOk1, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] at h
  obtain ⟨hs, hd, hsz, hg, hsg, hk, ha, hst, hca, ho, hrd, he, hrc, hf, hK, hcv, hat⟩ := h
  have hd' : data' = data := Array.toList_inj.mp hd
  have hc : acs' = acs := acs_eq_of_views hca (hcv.trans (restsOf_eq acs))
  subst hs hd' hsz hg hsg hk ha hst hf hK hc
  rcases m with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  simp only [Devm.output, Devm.returnData, Devm.error, Option.isNone_iff_eq_none] at ho hrd he
  subst ho hrd he
  rcases rc with _ | r
  · rcases atd with _ | _
    · rfl
    · simp only [atdOf1, Devm.accountsToDelete] at hat
      subst hat
      rfl
  · have hrc' := of_decide_eq_true hrc
    subst hrc'
    rcases atd with _ | _
    · rfl
    · simp only [atdOf1, Devm.accountsToDelete] at hat
      subst hat
      rfl

/-- A result decided at boundary `x` is `cfgOf1 x` at some world and bookkeeping. -/
theorem obsD1_cont {x : Bnd1} {r : Res} (h : obsD1 x r = obsDOk1 x) :
    ∃ m w, r = .cont (cfgOf1 x m w) := by
  rcases r with c | _ | _
  · exact ⟨_, _, congrArg Res.cont (cfg_of_obsD1 h)⟩
  · rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩; simp only [obsD1, obsDOk1,
    reduceCtorEq] at h
  · rcases x with ⟨_, _, _, _, _, _, _, _, _, _, _⟩; simp only [obsD1, obsDOk1,
    reduceCtorEq] at h

/-! ### A frame with two code-child calls -/

/-- The first stage of a two-call frame: from the result `r` of its prefix (up to its first
`CALL`), resume from the settled child `d` with the shadows `ck`/`ca`/`cs`/`cacc`, then
`n1` steps. -/
def callPairA (fs : List SFunc) (sta : Sevm) (ck : List (Adr × B256)) (ca : List Adr)
    (cs : StorShadow) (cacc : AcctShadow) (n1 : Nat) (r : Res) (d : Devm) : Res :=
  match r with
  | .cont c1 =>
    match callResume sta c1 d ck ca cs cacc with
    | some c2 => wrun fs sta n1 c2
    | none => .stuck
  | _ => .stuck

/-- The third stage: `n3` steps to the second `CALL`, its child run by its own program
`fsT` (`nT` steps), the resume from its halting configuration's shadows, then `n4` steps. -/
def callPairB (fs : List SFunc) (sta : Sevm) (fsT : List SFunc) (tcode : ByteArray)
    (n3 nT n4 : Nat) (c : Cfg) : Res :=
  match wrun fs sta n3 c with
  | .cont c3 =>
    match childRun fsT tcode sta nT c3 with
    | .done (.halted d2) cl =>
      match callResume sta c3 d2 cl.keys cl.adrs cl.stor cl.acs with
      | some c4 => wrun fs sta n4 c4
      | none => .stuck
    | _ => .stuck
  | _ => .stuck

/-- The whole of a two-call frame after its prefix (with result `r`): the first child `d`
supplied with the shadows `ck`/`ca`/`cs`/`cacc`, `nA` steps to the second `CALL`, its child
run by `fsT`, `nB` steps after it.  Taking the prefix's result as an argument lets a proof
about the rest case on it without the kernel evaluating the prefix. -/
def callPairFrom (fs : List SFunc) (sta : Sevm) (fsT : List SFunc) (tcode : ByteArray)
    (nA nT nB : Nat) (ck : List (Adr × B256)) (ca : List Adr) (cs : StorShadow)
    (cacc : AcctShadow) (r : Res) (d : Devm) : Res :=
  match r with
  | .cont c1 =>
    match callResume sta c1 d ck ca cs cacc with
    | some c2 =>
      match wrun fs sta nA c2 with
      | .cont c3 =>
        match childRun fsT tcode sta nT c3 with
        | .done (.halted d2) cl =>
          match callResume sta c3 d2 cl.keys cl.adrs cl.stor cl.acs with
          | some c4 => wrun fs sta nB c4
          | none => .stuck
        | _ => .stuck
      | _ => .stuck
    | none => .stuck
  | _ => .stuck

/-- The four stages compose, over any boundaries and any prefix result: `nA` is the first
stage's steps and the second's and third's up to the `CALL` (`nA = n1 + (n2 + n3)`), and
`nB` the third stage's after the resume and the fourth's (`nB = n4 + n5`).  Every
configuration the proof cases on is a variable, so the kernel evaluates nothing here. -/
theorem callPairFrom_stages {P : Res → Prop} {fs : List SFunc} {sta : Sevm} {fsT : List SFunc}
    {tcode : ByteArray} {nA nT nB n1 n2 n3 n4 n5 : Nat} {ck : List (Adr × B256)} {ca : List Adr}
    {cs : StorShadow} {cacc : AcctShadow} {r0 : Res} {d : Devm} {x1 x2 x3 : Bnd1}
    (hnA : nA = n1 + (n2 + n3)) (hnB : nB = n4 + n5)
    (h1 : obsD1 x1 (callPairA fs sta ck ca cs cacc n1 r0 d) = obsDOk1 x1)
    (h2 : ∀ m w, obsD1 x2 (wrun fs sta n2 (cfgOf1 x1 m w)) = obsDOk1 x2)
    (h3 : ∀ m w, obsD1 x3 (callPairB fs sta fsT tcode n3 nT n4 (cfgOf1 x2 m w)) = obsDOk1 x3)
    (h4 : ∀ m w, P (wrun fs sta n5 (cfgOf1 x3 m w))) :
    P (callPairFrom fs sta fsT tcode nA nT nB ck ca cs cacc r0 d) := by
  subst hnA hnB
  unfold callPairA at h1
  unfold callPairFrom
  rcases r0 with c1 | _ | _
  · dsimp only at h1 ⊢
    generalize callResume sta c1 d ck ca cs cacc = o at h1 ⊢
    rcases o with _ | c2
    · obtain ⟨_, _, e⟩ := obsD1_cont h1; cases e
    · dsimp only at h1 ⊢
      obtain ⟨m, w, e⟩ := obsD1_cont h1
      rw [wrun_add fs sta n1 (n2 + n3), e]
      dsimp only
      obtain ⟨m', w', e'⟩ := obsD1_cont (h2 m w)
      rw [wrun_add fs sta n2 n3, e']
      dsimp only
      have h3' := h3 m' w'
      unfold callPairB at h3'
      generalize wrun fs sta n3 (cfgOf1 x2 m' w') = r4 at h3' ⊢
      rcases r4 with c3 | _ | _
      · dsimp only at h3' ⊢
        generalize childRun fsT tcode sta nT c3 = r5 at h3' ⊢
        rcases r5 with _ | ⟨d2 | d2, cl⟩ | _
        all_goals try (dsimp only at h3'; obtain ⟨_, _, e⟩ := obsD1_cont h3'; cases e)
        dsimp only at h3' ⊢
        generalize callResume sta c3 d2 cl.keys cl.adrs cl.stor cl.acs = o4 at h3' ⊢
        rcases o4 with _ | c4
        · obtain ⟨_, _, e⟩ := obsD1_cont h3'; cases e
        · dsimp only at h3' ⊢
          obtain ⟨m'', w'', e''⟩ := obsD1_cont h3'
          rw [wrun_add fs sta n4 n5, e'']
          exact h4 m'' w''
      · obtain ⟨_, _, e⟩ := obsD1_cont h3'; cases e
      · obtain ⟨_, _, e⟩ := obsD1_cont h3'; cases e
  · obtain ⟨_, _, e⟩ := obsD1_cont h1; cases e
  · obtain ⟨_, _, e⟩ := obsD1_cont h1; cases e

end Blanc.Lift.Witness.Boundary
