import Blanc.Lift.Exact

/-!
# Loops in lifted code

A loop in a certificate is a goto (`jump k`, or a taken `branchTo _ k`) back to
an entry `k` that the loop body reaches again.  `SFunc.RunP` already admits such
runs, since a successful run is a finite derivation; this module states the
rules that reason about them one iteration at a time.

**Cut runs.**  `SFunc.RunCutP P fs sevm C` is `SFunc.RunP` with every goto to an
entry in the cut list `C` stopped: the run ends in `.at k devm` (control is about
to enter entry `k` in state `devm`) instead of continuing into the entry's tree.
Gotos to entries outside `C` are followed as in `RunP`.  An internal call's
callee runs under the uncut `SFunc.RunP`: loops inside a callee are the callee's
own business.  With `C = []` a cut run is exactly a run
(`SFunc.runP_iff_runCutP_nil`).

**Nesting.**  The safety rule `SFunc.RunCutP.loop` is stated relative to an
arbitrary outer cut list `C`, so a loop nested inside another loop's body is
handled by applying the rule again inside the outer body's cut run (inner head
`k₂`, outer list `k :: C`).  Solidity's inlined copy loops inside a Merkle-level
loop have this shape.

**Existence.**  `SFunc.RunExactCut` is the exact-gas sibling (the relation
`lift_exact` consumes).  `SFunc.RunExactCut.iterate` builds a whole loop run
from per-iteration cut runs, for proofs that a call succeeds.
-/

namespace Blanc.Lift

open Jaune

/-- Where a cut run stops: about to enter a cut entry, or finished. -/
inductive Seg : Type
  | at : Nat → Devm → Seg
  | done : Outcome → Seg

/-- `SFunc.RunP` with gotos into the cut list `C` stopped (see the module doc). -/
inductive SFunc.RunCutP (P : Sevm → Devm → Ninst → Devm → Prop) (fs : List SFunc)
    (sevm : Sevm) (C : List Nat) : Devm → SFunc → Seg → Prop
  | zero {devm devm' : Devm} {f g : SFunc} {r : Seg} (d : B256) :
    Devm.PopBurn [d, 0] devm devm' →
    SFunc.RunCutP P fs sevm C devm' f r →
    SFunc.RunCutP P fs sevm C devm (.branch f g) r
  | succ {devm devm' : Devm} {f g : SFunc} {r : Seg} (d w : B256) :
    w ≠ 0 →
    Devm.PopBurn [d, w] devm devm' →
    SFunc.RunCutP P fs sevm C devm' g r →
    SFunc.RunCutP P fs sevm C devm (.branch f g) r
  | toZero {devm devm' : Devm} {f : SFunc} {k : Nat} {r : Seg} (d : B256) :
    Devm.PopBurn [d, 0] devm devm' →
    SFunc.RunCutP P fs sevm C devm' f r →
    SFunc.RunCutP P fs sevm C devm (.branchTo f k) r
  | toSuccCut {devm devm' : Devm} {f : SFunc} {k : Nat} (d w : B256) :
    w ≠ 0 →
    k ∈ C →
    Devm.PopBurn [d, w] devm devm' →
    SFunc.RunCutP P fs sevm C devm (.branchTo f k) (.at k devm')
  | toSucc {devm devm' : Devm} {f g : SFunc} {k : Nat} {r : Seg} (d w : B256) :
    w ≠ 0 →
    k ∉ C →
    fs[k]? = some g →
    Devm.PopBurn [d, w] devm devm' →
    SFunc.RunCutP P fs sevm C devm' g r →
    SFunc.RunCutP P fs sevm C devm (.branchTo f k) r
  | last {devm devm' : Devm} {l : Linst} :
    Linst.Run sevm devm l (.ok devm') →
    SFunc.RunCutP P fs sevm C devm (.last l) (.done (.halted devm'))
  | next {devm devm' : Devm} {n : Ninst} {f : SFunc} {r : Seg} :
    P sevm devm n devm' →
    SFunc.RunCutP P fs sevm C devm' f r →
    SFunc.RunCutP P fs sevm C devm (.next n f) r
  | dest {devm devm' : Devm} {f : SFunc} {r : Seg} :
    Devm.Burn devm devm' →
    SFunc.RunCutP P fs sevm C devm' f r →
    SFunc.RunCutP P fs sevm C devm (.dest f) r
  | jumpCut {devm devm' : Devm} {k : Nat} (d : B256) :
    k ∈ C →
    Devm.PopBurn [d] devm devm' →
    SFunc.RunCutP P fs sevm C devm (.jump k) (.at k devm')
  | jump {devm devm' : Devm} {k : Nat} {f : SFunc} {r : Seg} (d : B256) :
    k ∉ C →
    fs[k]? = some f →
    Devm.PopBurn [d] devm devm' →
    SFunc.RunCutP P fs sevm C devm' f r →
    SFunc.RunCutP P fs sevm C devm (.jump k) r
  | ret {devm devm' : Devm} (d : B256) :
    Devm.PopBurn [d] devm devm' →
    SFunc.RunCutP P fs sevm C devm .ret (.done (.returned devm'))
  | callHalt {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} (d : B256) :
    fs[k]? = some g →
    Devm.PopBurn [d] devm devm' →
    SFunc.RunP P fs sevm devm' g (.halted devm'') →
    SFunc.RunCutP P fs sevm C devm (.callNext k f) (.done (.halted devm''))
  | callRet {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} {r : Seg} (d : B256) :
    fs[k]? = some g →
    Devm.PopBurn [d] devm devm' →
    SFunc.RunP P fs sevm devm' g (.returned devm'') →
    SFunc.RunCutP P fs sevm C devm'' f r →
    SFunc.RunCutP P fs sevm C devm (.callNext k f) r
  | pcAt {devm devm' : Devm} {p : Nat} {f : SFunc} {r : Seg} :
    P sevm devm (.reg .pc) devm' →
    Ninst.StepRun p sevm devm (.reg .pc) .none (.ok devm') →
    SFunc.RunCutP P fs sevm C devm' f r →
    SFunc.RunCutP P fs sevm C devm (.pcAt p f) r

/-- A cut run over Jaune's instruction steps. -/
abbrev SFunc.RunCut (fs : List SFunc) (sevm : Sevm) (C : List Nat) :
    Devm → SFunc → Seg → Prop :=
  SFunc.RunCutP Ninst.Run fs sevm C

/-- With nothing cut, a cut run is a run. -/
theorem SFunc.runP_iff_runCutP_nil {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {devm : Devm} {f : SFunc} {o : Outcome} :
    SFunc.RunP P fs sevm devm f o ↔ SFunc.RunCutP P fs sevm [] devm f (.done o) := by
  constructor
  · intro run
    induction run with
    | zero d pop _ ih => exact .zero d pop ih
    | succ d w hnz pop _ ih => exact .succ d w hnz pop ih
    | toZero d pop _ ih => exact .toZero d pop ih
    | toSucc d w hnz hget pop _ ih =>
      exact .toSucc d w hnz (by simp) (by simpa using hget) pop ih
    | last h => exact .last h
    | next h _ ih => exact .next h ih
    | dest burn _ ih => exact .dest burn ih
    | jump d hget pop _ ih => exact .jump d (by simp) (by simpa using hget) pop ih
    | ret d pop => exact .ret d pop
    | callHalt d hget pop run => exact .callHalt d (by simpa using hget) pop run
    | callRet d hget pop run cont ihRun ihTail =>
      exact .callRet d (by simpa using hget) pop run ihTail
    | pcAt h hpc _ ih => exact .pcAt h hpc ih
  · intro run
    have aux : ∀ {devm f r}, SFunc.RunCutP P fs sevm [] devm f r →
        ∀ o, r = .done o → SFunc.RunP P fs sevm devm f o := by
      intro devm f r run
      refine SFunc.RunCutP.rec
        (motive := fun devm f r _ => ∀ o, r = .done o →
          SFunc.RunP P fs sevm devm f o)
        (fun d pop hrun ih o heq => .zero d pop (ih o heq))
        (fun d w hnz pop hrun ih o heq => .succ d w hnz pop (ih o heq))
        (fun d pop hrun ih o heq => .toZero d pop (ih o heq))
        (fun d w hnz hk pop o heq => by simp at hk)
        (fun d w hnz hnot hget pop hrun ih o heq =>
          .toSucc d w hnz (by simpa using hget) pop (ih o heq))
        (fun h o heq => by cases heq; exact .last h)
        (fun h hrun ih o heq => .next h (ih o heq))
        (fun burn hrun ih o heq => .dest burn (ih o heq))
        (fun d hk pop o heq => by simp at hk)
        (fun d hnot hget pop hrun ih o heq =>
          .jump d (by simpa using hget) pop (ih o heq))
        (fun d pop o heq => by cases heq; exact .ret d pop)
        (fun d hget pop hrun o heq => by
          cases heq
          exact .callHalt d (by simpa using hget) pop hrun)
        (fun d hget pop hrun hcont ih o heq =>
          .callRet d (by simpa using hget) pop hrun (ih o heq))
        (fun h hpc hrun ih o heq => .pcAt h hpc (ih o heq))
        run
    exact aux run o rfl

/-- What one iteration of a loop at `k` must establish: re-entering `k` keeps the
invariant `I`, and every other way out (a cut entry of the outer list, or the end
of the run) satisfies `Q`. -/
def Seg.LoopPost (k : Nat) (I : Devm → Prop) (Q : Seg → Prop) : Seg → Prop
  | .at j d => if j = k then I d else Q (.at j d)
  | .done o => Q (.done o)

/-- **Loop rule.**  If every iteration of the loop at entry `k` (a run of its tree
cut at `k` and the outer list `C`) from a state satisfying `I` ends satisfying
`Seg.LoopPost k I Q`, then every run of the loop cut at `C` from a state
satisfying `I` ends satisfying `Q`. -/
theorem SFunc.RunCutP.loop {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {k : Nat} {g : SFunc}
    (hk : fs[k]? = some g) (hkC : k ∉ C)
    (I : Devm → Prop) (Q : Seg → Prop)
    (step : ∀ devm, I devm → ∀ r, SFunc.RunCutP P fs sevm (k :: C) devm g r →
      Seg.LoopPost k I Q r) :
    ∀ devm r, I devm → SFunc.RunCutP P fs sevm C devm g r → Q r := by
  intro devm r hI run
  have aux : ∀ {devm f r}, SFunc.RunCutP P fs sevm C devm f r →
      (∀ r', SFunc.RunCutP P fs sevm (k :: C) devm f r' →
        Seg.LoopPost k I Q r') → Q r := by
    intro devm f r run
    refine SFunc.RunCutP.rec (C := C)
      (motive := fun devm f r _ =>
        (∀ r', SFunc.RunCutP P fs sevm (k :: C) devm f r' →
          Seg.LoopPost k I Q r') → Q r)
      (fun d pop hrun ih H =>
        ih (fun r' h' => H r' (.zero d pop h')))
      (fun d w hnz pop hrun ih H =>
        ih (fun r' h' => H r' (.succ d w hnz pop h')))
      (fun d pop hrun ih H =>
        ih (fun r' h' => H r' (.toZero d pop h')))
      (fun {s0 s1 f0 t} d w hnz hk pop H => by
        have htk : t ≠ k := by
          intro h
          apply hkC
          simpa [h] using hk
        have hp := H _ (.toSuccCut d w hnz (List.mem_cons_of_mem k hk) pop)
        simpa [Seg.LoopPost, htk] using hp)
      (fun {s0 s1 f0 g0 t r0} d w hnz hnot hget pop hrun ih H => by
        by_cases htk : t = k
        · subst t
          have hfg : g = _ := Option.some.inj (hk.symm.trans hget)
          cases hfg
          have hp := H _ (.toSuccCut d w hnz (by simp) pop)
          have hInv : I s1 := by simpa [Seg.LoopPost] using hp
          exact ih (step s1 hInv)
        · have hnot' : t ∉ k :: C := by
            intro hm
            have hm' := List.mem_cons.mp hm
            rcases hm' with h | hm
            · exact htk h
            · exact hnot hm
          exact ih (fun r' h' => H r' (.toSucc d w hnz hnot' hget pop h')))
      (fun h H => by simpa [Seg.LoopPost] using H _ (.last h))
      (fun h hrun ih H =>
        ih (fun r' h' => H r' (.next h h')))
      (fun burn hrun ih H =>
        ih (fun r' h' => H r' (.dest burn h')))
      (fun {s0 s1 t} d hk pop H => by
        have htk : t ≠ k := by
          intro h
          apply hkC
          simpa [h] using hk
        have hp := H _ (.jumpCut d (List.mem_cons_of_mem k hk) pop)
        simpa [Seg.LoopPost, htk] using hp)
      (fun {s0 s1 t f0 r0} d hnot hget pop hrun ih H => by
        by_cases htk : t = k
        · subst t
          have hfg : g = _ := Option.some.inj (hk.symm.trans hget)
          cases hfg
          have hp := H _ (.jumpCut d (by simp) pop)
          have hInv : I s1 := by simpa [Seg.LoopPost] using hp
          exact ih (step s1 hInv)
        · have hnot' : t ∉ k :: C := by
            intro hm
            have hm' := List.mem_cons.mp hm
            rcases hm' with h | hm
            · exact htk h
            · exact hnot hm
          exact ih (fun r' h' => H r' (.jump d hnot' hget pop h')))
      (fun d pop H => by simpa [Seg.LoopPost] using H _ (.ret d pop))
      (fun d hget pop hrun H => by
        simpa [Seg.LoopPost] using H _ (.callHalt d hget pop hrun))
      (fun d hget pop hrun hcont ih H =>
        ih (fun r' h' => H r' (.callRet d hget pop hrun h')))
      (fun h hpc hrun ih H =>
        ih (fun r' h' => H r' (.pcAt h hpc h')))
      run
  exact aux run (step devm hI)

/-- The loop rule for a loop at the top level of a function (nothing else cut). -/
theorem SFunc.RunP.loop {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {k : Nat} {g : SFunc}
    (hk : fs[k]? = some g)
    (I : Devm → Prop) (Q : Outcome → Prop)
    (step : ∀ devm, I devm → ∀ r, SFunc.RunCutP P fs sevm [k] devm g r →
      match r with
      | .at _ devm' => I devm'
      | .done o => Q o) :
    ∀ devm o, I devm → SFunc.RunP P fs sevm devm g o → Q o := by
  intro devm o hI run
  have hcut : SFunc.RunCutP P fs sevm [] devm g (.done o) :=
    (SFunc.runP_iff_runCutP_nil (P := P)).mp run
  have hloop := SFunc.RunCutP.loop (P := P) (fs := fs) (sevm := sevm)
    (C := []) (k := k) (g := g) hk (by simp) I
    (fun r => match r with
      | .at _ d => I d
      | .done o => Q o) (by
      intro d hI r hrun
      have hp := step d hI r hrun
      cases r <;> simpa [Seg.LoopPost] using hp)
  exact hloop devm (.done o) hI hcut

/-! ## Exact-gas cut runs -/

/-- `SFunc.RunExact` with gotos into the cut list `C` stopped. -/
inductive SFunc.RunExactCut (fs : List SFunc) (sevm : Sevm) (C : List Nat) :
    Devm → SFunc → Seg → Prop
  | zero {devm devm' : Devm} {f g : SFunc} {r : Seg} (d : B256) :
    Devm.PopBurnBy [d, 0] gHigh devm devm' →
    SFunc.RunExactCut fs sevm C devm' f r →
    SFunc.RunExactCut fs sevm C devm (.branch f g) r
  | succ {devm devm' : Devm} {f g : SFunc} {r : Seg} (d w : B256) :
    w ≠ 0 →
    Devm.PopBurnBy [d, w] gHigh devm devm' →
    SFunc.RunExactCut fs sevm C devm' g r →
    SFunc.RunExactCut fs sevm C devm (.branch f g) r
  | toZero {devm devm' : Devm} {f : SFunc} {k : Nat} {r : Seg} (d : B256) :
    Devm.PopBurnBy [d, 0] gHigh devm devm' →
    SFunc.RunExactCut fs sevm C devm' f r →
    SFunc.RunExactCut fs sevm C devm (.branchTo f k) r
  | toSuccCut {devm devm' : Devm} {f : SFunc} {k : Nat} (d w : B256) :
    w ≠ 0 →
    k ∈ C →
    Devm.PopBurnBy [d, w] gHigh devm devm' →
    SFunc.RunExactCut fs sevm C devm (.branchTo f k) (.at k devm')
  | toSucc {devm devm' : Devm} {f g : SFunc} {k : Nat} {r : Seg} (d w : B256) :
    w ≠ 0 →
    k ∉ C →
    fs[k]? = some g →
    Devm.PopBurnBy [d, w] gHigh devm devm' →
    SFunc.RunExactCut fs sevm C devm' g r →
    SFunc.RunExactCut fs sevm C devm (.branchTo f k) r
  | last {devm devm' : Devm} {l : Linst} :
    Linst.Run sevm devm l (.ok devm') →
    SFunc.RunExactCut fs sevm C devm (.last l) (.done (.halted devm'))
  | next {devm devm' : Devm} {n : Ninst} {f : SFunc} {r : Seg} :
    Ninst.RunCompiled sevm devm n devm' →
    SFunc.RunExactCut fs sevm C devm' f r →
    SFunc.RunExactCut fs sevm C devm (.next n f) r
  | dest {devm devm' : Devm} {f : SFunc} {r : Seg} :
    Devm.BurnBy gJumpdest devm devm' →
    SFunc.RunExactCut fs sevm C devm' f r →
    SFunc.RunExactCut fs sevm C devm (.dest f) r
  | jumpCut {devm devm' : Devm} {k : Nat} (d : B256) :
    k ∈ C →
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExactCut fs sevm C devm (.jump k) (.at k devm')
  | jump {devm devm' : Devm} {k : Nat} {f : SFunc} {r : Seg} (d : B256) :
    k ∉ C →
    fs[k]? = some f →
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExactCut fs sevm C devm' f r →
    SFunc.RunExactCut fs sevm C devm (.jump k) r
  | ret {devm devm' : Devm} (d : B256) :
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExactCut fs sevm C devm .ret (.done (.returned devm'))
  | callHalt {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} (d : B256) :
    fs[k]? = some g →
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExact fs sevm devm' g (.halted devm'') →
    SFunc.RunExactCut fs sevm C devm (.callNext k f) (.done (.halted devm''))
  | callRet {devm devm' devm'' : Devm} {k : Nat} {f g : SFunc} {r : Seg} (d : B256) :
    fs[k]? = some g →
    Devm.PopBurnBy [d] gMid devm devm' →
    SFunc.RunExact fs sevm devm' g (.returned devm'') →
    SFunc.RunExactCut fs sevm C devm'' f r →
    SFunc.RunExactCut fs sevm C devm (.callNext k f) r
  | pcAt {devm devm' : Devm} {p : Nat} {f : SFunc} {r : Seg} :
    Ninst.StepRun p sevm devm (.reg .pc) .none (.ok devm') →
    SFunc.RunExactCut fs sevm C devm' f r →
    SFunc.RunExactCut fs sevm C devm (.pcAt p f) r

/-- With nothing cut, an exact cut run is an exact run. -/
theorem SFunc.runExact_iff_runExactCut_nil {fs : List SFunc} {sevm : Sevm}
    {devm : Devm} {f : SFunc} {o : Outcome} :
    SFunc.RunExact fs sevm devm f o ↔ SFunc.RunExactCut fs sevm [] devm f (.done o) := by
  constructor
  · intro run
    induction run with
    | zero d hpop hrun ih => exact .zero d hpop ih
    | succ d w hnz hpop hrun ih => exact .succ d w hnz hpop ih
    | toZero d hpop hrun ih => exact .toZero d hpop ih
    | toSucc d w hnz hget hpop hrun ih =>
      exact .toSucc d w hnz (by simp) hget hpop ih
    | last h => exact .last h
    | next h hrun ih => exact .next h ih
    | dest hburn hrun ih => exact .dest hburn ih
    | jump d hget hpop hrun ih => exact .jump d (by simp) hget hpop ih
    | ret d hpop => exact .ret d hpop
    | callHalt d hget hpop hrun => exact .callHalt d hget hpop hrun
    | callRet d hget hpop hrun hcont ihrun ihcont =>
      exact .callRet d hget hpop hrun ihcont
    | pcAt hpc hrun ih => exact .pcAt hpc ih
  · intro run
    have aux : ∀ {devm f r}, SFunc.RunExactCut fs sevm [] devm f r →
        ∀ o, r = .done o → SFunc.RunExact fs sevm devm f o := by
      intro devm f r run
      refine SFunc.RunExactCut.rec
        (motive := fun devm f r _ => ∀ o, r = .done o →
          SFunc.RunExact fs sevm devm f o)
        (fun d hpop hrun ih o heq => .zero d hpop (ih o heq))
        (fun d w hnz hpop hrun ih o heq => .succ d w hnz hpop (ih o heq))
        (fun d hpop hrun ih o heq => .toZero d hpop (ih o heq))
        (fun d w hnz hk hpop o heq => by simp at hk)
        (fun d w hnz hnot hget hpop hrun ih o heq =>
          .toSucc d w hnz hget hpop (ih o heq))
        (fun h o heq => by cases heq; exact .last h)
        (fun h hrun ih o heq => .next h (ih o heq))
        (fun hburn hrun ih o heq => .dest hburn (ih o heq))
        (fun d hk hpop o heq => by simp at hk)
        (fun d hnot hget hpop hrun ih o heq =>
          .jump d hget hpop (ih o heq))
        (fun d hpop o heq => by cases heq; exact .ret d hpop)
        (fun d hget hpop hrun o heq => by
          cases heq
          exact .callHalt d hget hpop hrun)
        (fun d hget hpop hrun hcont ih o heq =>
          .callRet d hget hpop hrun (ih o heq))
        (fun hpc hrun ih o heq => .pcAt hpc (ih o heq))
        run
    exact aux run o rfl

theorem SFunc.RunExactCut.resume {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {j : Nat} {g : SFunc} (hj : fs[j]? = some g) (hjC : j ∉ C)
    {devm devm' : Devm} {f : SFunc} {r : Seg}
    (seg : SFunc.RunExactCut fs sevm (j :: C) devm f (.at j devm'))
    (rest : SFunc.RunExactCut fs sevm C devm' g r) :
    SFunc.RunExactCut fs sevm C devm f r := by
  have aux : ∀ {devm f r} d,
      SFunc.RunExactCut fs sevm (j :: C) devm f r → r = .at j d →
        ∀ r', SFunc.RunExactCut fs sevm C d g r' →
          SFunc.RunExactCut fs sevm C devm f r' := by
    intro devm f r d seg
    refine SFunc.RunExactCut.rec (C := j :: C)
      (motive := fun devm f r _ => ∀ d, r = .at j d →
        ∀ r', SFunc.RunExactCut fs sevm C d g r' →
          SFunc.RunExactCut fs sevm C devm f r')
      (fun d0 pop hrun ih d heq r' rest => .zero d0 pop (ih d heq r' rest))
      (fun d0 w hnz pop hrun ih d heq r' rest => .succ d0 w hnz pop (ih d heq r' rest))
      (fun d0 pop hrun ih d heq r' rest => .toZero d0 pop (ih d heq r' rest))
      (fun d0 w hnz hk pop d heq r' rest => by
        cases heq
        exact .toSucc d0 w hnz hjC hj pop rest)
      (fun d0 w hnz hnot hget pop hrun ih d heq r' rest =>
        .toSucc d0 w hnz (fun hk => hnot (List.mem_cons_of_mem j hk))
          hget pop (ih d heq r' rest))
      (fun h d heq r' rest => by cases heq)
      (fun h hrun ih d heq r' rest => .next h (ih d heq r' rest))
      (fun burn hrun ih d heq r' rest => .dest burn (ih d heq r' rest))
      (fun d0 hk pop d heq r' rest => by
        cases heq
        exact .jump d0 hjC hj pop rest)
      (fun d0 hnot hget pop hrun ih d heq r' rest =>
        .jump d0 (fun hk => hnot (List.mem_cons_of_mem j hk))
          hget pop (ih d heq r' rest))
      (fun d0 pop d heq r' rest => by cases heq)
      (fun d0 hget pop hrun d heq r' rest => by cases heq)
      (fun d0 hget pop hrun hcont ih d heq r' rest =>
        .callRet d0 hget pop hrun (ih d heq r' rest))
      (fun hpc hrun ih d heq r' rest => .pcAt hpc (ih d heq r' rest))
      seg d
  exact aux devm' seg rfl r rest

theorem SFunc.RunExactCut.uncut {fs : List SFunc} {sevm : Sevm} {C : List Nat} {j : Nat}
    {devm : Devm} {f : SFunc} {r : Seg}
    (seg : SFunc.RunExactCut fs sevm (j :: C) devm f r)
    (hr : ∀ d, r ≠ .at j d) :
    SFunc.RunExactCut fs sevm C devm f r := by
  refine SFunc.RunExactCut.rec
    (motive := fun devm f r _ => (∀ d, r ≠ .at j d) →
      SFunc.RunExactCut fs sevm C devm f r)
    (fun d pop hrun ih hr => .zero d pop (ih hr))
    (fun d w hnz pop hrun ih hr => .succ d w hnz pop (ih hr))
    (fun d pop hrun ih hr => .toZero d pop (ih hr))
    (fun d w hnz hk pop hr => by
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact False.elim (hr _ rfl)
      · exact .toSuccCut d w hnz hk pop)
    (fun d w hnz hnot hget pop hrun ih hr =>
      .toSucc d w hnz (fun hk => hnot (List.mem_cons_of_mem j hk))
        hget pop (ih hr))
    (fun h hr => .last h)
    (fun h hrun ih hr => .next h (ih hr))
    (fun burn hrun ih hr => .dest burn (ih hr))
    (fun d hk pop hr => by
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact False.elim (hr _ rfl)
      · exact .jumpCut d hk pop)
    (fun d hnot hget pop hrun ih hr =>
      .jump d (fun hk => hnot (List.mem_cons_of_mem j hk)) hget pop (ih hr))
    (fun d pop hr => .ret d pop)
    (fun d hget pop hrun hr => .callHalt d hget pop hrun)
    (fun d hget pop hrun hcont ih hr => .callRet d hget pop hrun (ih hr))
    (fun hpc hrun ih hr => .pcAt hpc (ih hr))
    seg hr

/-- **Loop construction.**  `N` iterations of the loop at entry `k`, each an exact
run of its tree cut at `k` from `J i` to `J (i + 1)`, followed by a final pass from
`J N` that leaves without re-entering `k`, make one exact run of the loop cut at
`C`. -/
theorem SFunc.RunExactCut.iterate {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {k : Nat} {g : SFunc} (hk : fs[k]? = some g) (hkC : k ∉ C)
    (J : Nat → Devm → Prop) (N : Nat) (R : Seg → Prop)
    (body : ∀ i, i < N → ∀ devm, J i devm →
      ∃ devm', SFunc.RunExactCut fs sevm (k :: C) devm g (.at k devm') ∧ J (i + 1) devm')
    (exit : ∀ devm, J N devm →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) devm g r ∧ (∀ d, r ≠ .at k d) ∧ R r) :
    ∀ devm, J 0 devm → ∃ r, SFunc.RunExactCut fs sevm C devm g r ∧ R r := by
  have aux : ∀ m i, i + m = N → ∀ devm, J i devm →
      ∃ r, SFunc.RunExactCut fs sevm C devm g r ∧ R r := by
    intro m
    induction m with
    | zero =>
      intro i hi devm hJ
      have hiN : i = N := by omega
      obtain ⟨r, hrun, hne, hR⟩ := exit devm (by simpa [hiN] using hJ)
      exact ⟨r, SFunc.RunExactCut.uncut hrun hne, hR⟩
    | succ m ih =>
      intro i hi devm hJ
      have hlt : i < N := by omega
      obtain ⟨devm', hbody, hJ'⟩ := body i hlt devm hJ
      obtain ⟨r, hrun, hR⟩ := ih (i + 1) (by omega) devm' hJ'
      exact ⟨r, SFunc.RunExactCut.resume hk hkC hbody hrun, hR⟩
  exact aux N 0 (by simp)

end Blanc.Lift
