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

/-- A cut run over Jaune's instruction steps. -/
abbrev SFunc.RunCut (fs : List SFunc) (sevm : Sevm) (C : List Nat) :
    Devm → SFunc → Seg → Prop :=
  SFunc.RunCutP Ninst.Run fs sevm C

theorem SFunc.RunCutP.mono {P Q : Sevm → Devm → Ninst → Devm → Prop}
    (hPQ : ∀ {s d n d'}, P s d n d' → Q s d n d')
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {devm : Devm} {f : SFunc} {r : Seg}
    (run : SFunc.RunCutP P fs sevm C devm f r) : SFunc.RunCutP Q fs sevm C devm f r := by
  sorry

/-- With nothing cut, a cut run is a run. -/
theorem SFunc.runP_iff_runCutP_nil {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {devm : Devm} {f : SFunc} {o : Outcome} :
    SFunc.RunP P fs sevm devm f o ↔ SFunc.RunCutP P fs sevm [] devm f (.done o) := by
  sorry

/-- With nothing cut, a cut run never stops at an entry. -/
theorem SFunc.RunCutP.nil_not_at {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {devm devm' : Devm} {f : SFunc} {k : Nat} :
    ¬ SFunc.RunCutP P fs sevm [] devm f (.at k devm') := by
  sorry

/-- A run cut at `j` that stopped at `j` resumes with a run from `j`'s tree. -/
theorem SFunc.RunCutP.resume {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {j : Nat} {g : SFunc}
    (hj : fs[j]? = some g) (hjC : j ∉ C)
    {devm devm' : Devm} {f : SFunc} {r : Seg}
    (seg : SFunc.RunCutP P fs sevm (j :: C) devm f (.at j devm'))
    (rest : SFunc.RunCutP P fs sevm C devm' g r) :
    SFunc.RunCutP P fs sevm C devm f r := by
  sorry

/-- A run cut at `j` that did not stop at `j` never reached `j`: it is a run cut
at the rest of the list, with the same result. -/
theorem SFunc.RunCutP.uncut {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {j : Nat}
    {devm : Devm} {f : SFunc} {r : Seg}
    (seg : SFunc.RunCutP P fs sevm (j :: C) devm f r)
    (hr : ∀ d, r ≠ .at j d) :
    SFunc.RunCutP P fs sevm C devm f r := by
  sorry

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
  sorry

/-- The loop rule with an iteration index: `J i` holds on the `i`-th entry to the
loop head. -/
theorem SFunc.RunCutP.loop_indexed {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {k : Nat} {g : SFunc}
    (hk : fs[k]? = some g) (hkC : k ∉ C)
    (J : Nat → Devm → Prop) (Q : Seg → Prop)
    (step : ∀ i devm, J i devm → ∀ r, SFunc.RunCutP P fs sevm (k :: C) devm g r →
      Seg.LoopPost k (J (i + 1)) Q r) :
    ∀ i devm r, J i devm → SFunc.RunCutP P fs sevm C devm g r → Q r := by
  sorry

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
  sorry

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

/-- An exact cut run is a cut run. -/
theorem SFunc.RunExactCut.toRunCut {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {devm : Devm} {f : SFunc} {r : Seg}
    (run : SFunc.RunExactCut fs sevm C devm f r) : SFunc.RunCut fs sevm C devm f r := by
  sorry

/-- With nothing cut, an exact cut run is an exact run. -/
theorem SFunc.runExact_iff_runExactCut_nil {fs : List SFunc} {sevm : Sevm}
    {devm : Devm} {f : SFunc} {o : Outcome} :
    SFunc.RunExact fs sevm devm f o ↔ SFunc.RunExactCut fs sevm [] devm f (.done o) := by
  sorry

theorem SFunc.RunExactCut.resume {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {j : Nat} {g : SFunc} (hj : fs[j]? = some g) (hjC : j ∉ C)
    {devm devm' : Devm} {f : SFunc} {r : Seg}
    (seg : SFunc.RunExactCut fs sevm (j :: C) devm f (.at j devm'))
    (rest : SFunc.RunExactCut fs sevm C devm' g r) :
    SFunc.RunExactCut fs sevm C devm f r := by
  sorry

theorem SFunc.RunExactCut.uncut {fs : List SFunc} {sevm : Sevm} {C : List Nat} {j : Nat}
    {devm : Devm} {f : SFunc} {r : Seg}
    (seg : SFunc.RunExactCut fs sevm (j :: C) devm f r)
    (hr : ∀ d, r ≠ .at j d) :
    SFunc.RunExactCut fs sevm C devm f r := by
  sorry

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
  sorry

end Blanc.Lift
