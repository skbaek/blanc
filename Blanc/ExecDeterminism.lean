import Blanc.Semantics

namespace Blanc

open Jaune

/-- Two executions from the same machine state have the same indexed result. -/
theorem Exec.result_unique {pc : Nat} {sevm : Sevm} {devm : Devm}
    {aout bout : Execution} (a : Exec pc sevm devm aout)
    (b : Exec pc sevm devm bout) : aout = bout := by
  have ha := (exec_iff_exec_eq pc sevm devm aout).mp ⟨a⟩
  have hb := (exec_iff_exec_eq pc sevm devm bout).mp ⟨b⟩
  exact ha.symm.trans hb

/-- An `Exec` derivation is uniquely determined by its indexed input and result. -/
theorem Exec.unique {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution}
    (a b : Exec pc sevm devm ex) : a = b := by
  induction a <;> cases b <;> simp_all <;>
    aesop (add safe forward Exec.result_unique)

instance {pc : Nat} {sevm : Sevm} {devm : Devm} {ex : Execution} :
    Subsingleton (Exec pc sevm devm ex) where
  allEq := Exec.unique

/-- A filled recursive slot and its step result are uniquely determined by
the nonrecursive machine step.  In the spawning case the entered child
machine is fixed, and `Exec.result_unique` pins the child's raw outcome. -/
theorem Step.Run.unique_of_filled
    {step : Step} {leftSlot rightSlot : Xlot}
    {leftOut rightOut : Execution}
    (leftFilled : leftSlot.Filled) (rightFilled : rightSlot.Filled)
    (leftRun : Step.Run step leftSlot leftOut)
    (rightRun : Step.Run step rightSlot rightOut) :
    leftSlot = rightSlot ∧ leftOut = rightOut := by
  cases step with
  | halt out =>
      simp [Step.Run] at leftRun rightRun
      simp_all
  | cont pc post =>
      simp [Step.Run] at leftRun rightRun
      simp_all
  | spawn frame resume pc =>
      simp only [Step.Run] at leftRun rightRun
      rcases leftRun with ⟨leftResult, leftFrame, leftOutEq⟩
      rcases rightRun with ⟨rightResult, rightFrame, rightOutEq⟩
      cases henter : frame.enter with
      | done result =>
          simp [RunFrame, henter] at leftFrame rightFrame
          simp_all
      | run evm =>
          simp [RunFrame, henter] at leftFrame rightFrame
          rcases leftFrame with ⟨leftRaw, leftSlotEq, leftResultEq⟩
          rcases rightFrame with ⟨rightRaw, rightSlotEq, rightResultEq⟩
          subst leftSlot
          subst rightSlot
          simp only [Xlot.Filled] at leftFilled rightFilled
          rcases leftFilled with ⟨leftExec⟩
          rcases rightFilled with ⟨rightExec⟩
          have hraw : leftRaw = rightRaw :=
            Exec.result_unique leftExec rightExec
          subst rightRaw
          simp_all

end Blanc
