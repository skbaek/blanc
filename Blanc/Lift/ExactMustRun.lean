import Blanc.Lift.Exact
import Blanc.CommonProofs
import Blanc.CompiledWalkInversion

/-!
# Instructions every successful exact run must execute

`SFunc.mustRun p K f` is a finite Boolean walk over a lifted tree: it holds when every successful
`SFunc.RunExact` derivation from `f` executes an instruction selected by `p`.  A straight node
selected by `p` ends the walk; any other straight node continues; a branch needs both arms; a
goto, jump or internal call needs its target entry to be among the assumed entries `K`; a
`REVERT` leaf has no successful run; `RET` and every other terminal fail the walk.
`SFunc.mustRunEntries p fs K` checks the assumption for every entry of `K` against the program.

`SFunc.RunExact.of_mustRun` turns the two checks into any fact `P` that one successful step of
a selected instruction implies.  The proof is an induction on the (finite) derivation, so loops
through `K` are covered.  `Ninst.isShift` with `Ninst.RunCompiled.shifts_of_isShift` is the
instance that extracts the selected `rules.op.shifts` capability from a fixed run witness;
`CoveredFork.rules_shifts` supplies it from fork coverage.
-/

namespace Blanc.Lift

open Jaune

/-- Every successful run of the tree executes an instruction selected by `p`, assuming the same
of the entries `K`. -/
def SFunc.mustRun (p : Ninst → Bool) (K : List Nat) : SFunc → Bool
  | .branch f g => SFunc.mustRun p K f && SFunc.mustRun p K g
  | .branchTo f k => SFunc.mustRun p K f && decide (k ∈ K)
  | .last l => decide (l = .revert)
  | .next n f => p n || SFunc.mustRun p K f
  | .dest f => SFunc.mustRun p K f
  | .jump k => decide (k ∈ K)
  | .callNext k _ => decide (k ∈ K)
  | .ret => false
  | .pcAt _ f => SFunc.mustRun p K f
  | .undefined => true

/-- Every entry of `K` present in `fs` passes `SFunc.mustRun p K`. -/
def SFunc.mustRunEntries (p : Ninst → Bool) (fs : List SFunc) (K : List Nat) : Bool :=
  K.all fun k =>
    match fs[k]? with
    | some g => SFunc.mustRun p K g
    | none => true

theorem SFunc.mustRunEntries_get {p : Ninst → Bool} {fs : List SFunc} {K : List Nat}
    (hK : SFunc.mustRunEntries p fs K = true) {k : Nat} {g : SFunc} (hk : decide (k ∈ K) = true)
    (hg : fs[k]? = some g) : SFunc.mustRun p K g = true := by
  have h := List.all_eq_true.mp hK k (of_decide_eq_true hk)
  rw [hg] at h
  exact h

/-- **A successful exact run passes a selected instruction.**  Any fact `P` that a successful
step of a selected instruction implies holds of every successful run of a tree passing
`SFunc.mustRun p K`, when the entries `K` pass it too. -/
theorem SFunc.RunExact.of_mustRun {fs : List SFunc} {sevm : Sevm} {p : Ninst → Bool}
    {K : List Nat} {P : Prop}
    (hp : ∀ {n : Ninst} {d d' : Devm}, p n = true → Ninst.RunCompiled sevm d n d' → P)
    (hK : SFunc.mustRunEntries p fs K = true) {d : Devm} {f : SFunc} {o : Outcome}
    (h : SFunc.RunExact fs sevm d f o) (hf : SFunc.mustRun p K f = true) : P := by
  induction h with
  | zero _ _ _ ih =>
    simp only [SFunc.mustRun, Bool.and_eq_true] at hf
    exact ih hf.1
  | succ _ _ _ _ _ ih =>
    simp only [SFunc.mustRun, Bool.and_eq_true] at hf
    exact ih hf.2
  | toZero _ _ _ ih =>
    simp only [SFunc.mustRun, Bool.and_eq_true] at hf
    exact ih hf.1
  | toSucc _ _ _ hget _ _ ih =>
    simp only [SFunc.mustRun, Bool.and_eq_true] at hf
    exact ih (SFunc.mustRunEntries_get hK hf.2 hget)
  | last hrun =>
    simp only [SFunc.mustRun] at hf
    cases of_decide_eq_true hf
    exact (Linst.not_run_revert_ok hrun).elim
  | next hn _ ih =>
    simp only [SFunc.mustRun, Bool.or_eq_true] at hf
    rcases hf with hsel | hrest
    · exact hp hsel hn
    · exact ih hrest
  | dest _ _ ih => exact ih hf
  | jump _ hget _ _ ih => exact ih (SFunc.mustRunEntries_get hK hf hget)
  | ret _ _ => exact absurd hf Bool.false_ne_true
  | callHalt _ hget _ _ ih => exact ih (SFunc.mustRunEntries_get hK hf hget)
  | callRet _ hget _ _ _ ih _ => exact ih (SFunc.mustRunEntries_get hK hf hget)
  | pcAt _ _ ih => exact ih hf

/-- The shift instructions, each available only under the selected `rules.op.shifts`. -/
def Ninst.isShift : Ninst → Bool
  | .reg .shl => true
  | .reg .shr => true
  | .reg .sar => true
  | _ => false

/-- A successful shift step witnesses the selected shift capability. -/
theorem Ninst.RunCompiled.shifts_of_isShift {sevm : Sevm} {n : Ninst} {d d' : Devm}
    (hn : Ninst.isShift n = true) (run : Ninst.RunCompiled sevm d n d') :
    sevm.benvStat.rules.op.shifts = true := by
  cases n with
  | reg r =>
    rcases of_run_reg (Ninst.Run.of_runCompiled run) with ⟨_, step⟩
    cases r <;> simp only [Ninst.isShift, Bool.false_eq_true] at hn <;>
    · simp only [Rinst.run, Rinst.runCore] at step
      split at step
      · assumption
      · cases step
  | _ => simp only [Ninst.isShift, Bool.false_eq_true] at hn

/-- **Selected shifts from a fixed run witness.** -/
theorem SFunc.RunExact.shifts_of_mustRun {fs : List SFunc} {sevm : Sevm} {K : List Nat}
    (hK : SFunc.mustRunEntries Ninst.isShift fs K = true) {d : Devm} {f : SFunc} {o : Outcome}
    (h : SFunc.RunExact fs sevm d f o) (hf : SFunc.mustRun Ninst.isShift K f = true) :
    sevm.benvStat.rules.op.shifts = true :=
  SFunc.RunExact.of_mustRun Ninst.RunCompiled.shifts_of_isShift hK h hf

/-- Every covered fork selects the shift instructions. -/
theorem _root_.Blanc.CoveredFork.rules_shifts {s : BenvStat} (h : CoveredFork s.fork) :
    s.rules.op.shifts = true :=
  h.cases (motive := fun f => (Fork.ruleSet f).op.shifts = true) rfl rfl rfl rfl

end Blanc.Lift
