import Blanc.ExecutionCodeAt
import Blanc.LadderBase

/-! Actual creation collision guards, shared below runtime-safety and chronology. -/
namespace Blanc

open Jaune

/-- A CREATE-family opcode produces a creation frame when state gas is absent. -/
theorem Xinst.step_create_isCreate_noStateGas
    {sevm : Sevm} {pre : Devm} {x : Xinst} {frame : Frame} {resume : Resume}
    (hsg : sevm.benvStat.rules.stateGas = none) (create : x = .create ∨ x = .create2)
    (spawn : Xinst.step sevm pre x = .spawn frame resume) :
    frame.isCreate = true := by
  rcases create with rfl | rfl <;>
    simp only [Xinst.step, hsg, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at spawn
  all_goals repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | solve | cases spawn
    | exact genericCreate.step_spawn_isCreate spawn

/-- The actual creation collision guard excludes a protected target. -/
theorem Evm.step_spawn_create_unprotected_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (create : frame.isCreate = true) :
    ¬ State.Protected pre.state frame.inner.currentTarget := by
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, address, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · have unprotected := genericCreate_step_spawn_target_unprotected spawn
    obtain ⟨rfl, rfl⟩ := genericCreate_step_spawn_exact spawn
    change ¬ State.Protected pre.state address
    rw [hprefix.state]
    exact unprotected
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    cases create


end Blanc
