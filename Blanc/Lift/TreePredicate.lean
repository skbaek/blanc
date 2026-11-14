import Blanc.Lift.Silent

/-!
# Observations of checked synthetic trees

One checker records allowed nonterminal and terminal instructions. The run fold
uses local observation laws and the original closed internal-entry table.
PC nodes retain the existing checker behavior and need a separate allowed-PC law.
-/

namespace Blanc.Lift

open Jaune

/-- Check ordinary steps and terminals; `pcAt` is handled by the fold's PC law. -/
def SFunc.stepsLastsSatisfy (next : Ninst → Bool) (last : Linst → Bool) : SFunc → Bool
  | .branch f g => f.stepsLastsSatisfy next last && g.stepsLastsSatisfy next last
  | .branchTo f _ => f.stepsLastsSatisfy next last
  | .last l => last l
  | .next n f => next n && f.stepsLastsSatisfy next last
  | .dest f => f.stepsLastsSatisfy next last
  | .jump _ => true
  | .callNext _ f => f.stepsLastsSatisfy next last
  | .ret => true
  | .pcAt _ f => f.stepsLastsSatisfy next last
  | .undefined => true

/-- Every admitted entry passes `check` and refers only to admitted entries. -/
def ClosedEntrySet (check : SFunc → Bool) (fs : List SFunc) (entries : List Nat) : Bool :=
  entries.all fun k => match fs[k]? with
    | some f => check f && f.refs.all (· ∈ entries)
    | none => false

theorem ClosedEntrySet.lookup {check : SFunc → Bool} {fs : List SFunc}
    {entries : List Nat} (closed : ClosedEntrySet check fs entries = true)
    {k : Nat} {f : SFunc} (member : k ∈ entries) (found : fs[k]? = some f) :
    check f = true ∧ f.refs.all (· ∈ entries) = true := by
  have h := (List.all_eq_true.mp closed) k member
  rw [found] at h
  simpa only [Bool.and_eq_true] using h

/-- Fold local observation equalities through the same successful synthetic run. -/
theorem SFunc.Run.observation_eq {α : Type} (observe : Devm → α)
    (next : Ninst → Bool) (last : Linst → Bool)
    {fs : List SFunc} {entries : List Nat} {sevm : Sevm}
    (pop : ∀ {ws : List B256} {a b : Devm},
      Devm.PopBurn ws a b → observe b = observe a)
    (burn : ∀ {a b : Devm}, Devm.Burn a b → observe b = observe a)
    (step : ∀ {a b : Devm} {n : Ninst},
      next n = true → Ninst.Run sevm a n b → observe b = observe a)
    (terminal : ∀ {a b : Devm} {l : Linst},
      last l = true → Linst.Run sevm a l (.ok b) → observe b = observe a)
    (pc : next (.reg .pc) = true)
    (closed : ClosedEntrySet (fun f => f.stepsLastsSatisfy next last) fs entries = true)
    {pre : Devm} {f : SFunc} {out : Outcome}
    (checked : f.stepsLastsSatisfy next last = true)
    (refs : f.refs.all (· ∈ entries) = true)
    (run : SFunc.Run fs sevm pre f out) : observe (Outcome.devm out) = observe pre := by
  induction run with
  | zero _ popped _ ih =>
      simp only [SFunc.stepsLastsSatisfy, Bool.and_eq_true] at checked
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at refs
      exact (ih checked.1 refs.1).trans (pop popped)
  | succ _ _ _ popped _ ih =>
      simp only [SFunc.stepsLastsSatisfy, Bool.and_eq_true] at checked
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at refs
      exact (ih checked.2 refs.2).trans (pop popped)
  | toZero _ popped _ ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      exact (ih checked refs.2).trans (pop popped)
  | toSucc _ _ _ found popped _ ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      have target := ClosedEntrySet.lookup closed (of_decide_eq_true refs.1) found
      exact (ih target.1 target.2).trans (pop popped)
  | last executed => exact terminal checked executed
  | next executed _ ih =>
      simp only [SFunc.stepsLastsSatisfy, Bool.and_eq_true] at checked
      exact (ih checked.2 refs).trans (step checked.1 executed)
  | dest burned _ ih => exact (ih checked refs).trans (burn burned)
  | jump _ found popped _ ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      have target := ClosedEntrySet.lookup closed (of_decide_eq_true refs.1) found
      exact (ih target.1 target.2).trans (pop popped)
  | ret _ popped => exact pop popped
  | callHalt _ found popped _ ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      have target := ClosedEntrySet.lookup closed (of_decide_eq_true refs.1) found
      exact (ih target.1 target.2).trans (pop popped)
  | callRet _ found popped _ _ ihCall ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      have target := ClosedEntrySet.lookup closed (of_decide_eq_true refs.1) found
      exact (ihTail checked refs.2).trans ((ihCall target.1 target.2).trans (pop popped))
  | pcAt executed _ _ ih => exact (ih checked refs).trans (step pc executed)

end Blanc.Lift
