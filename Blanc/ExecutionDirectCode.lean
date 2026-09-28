import Blanc.CommonProofs

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-- STATICCALL has the same direct-code property as CALL. -/
theorem Xinst.step_staticcall_sameTarget_code
    {sevm : Sevm} {devm : Devm} {f : Jaune.Frame} {rsm : Resume}
    (spawn : Jaune.Xinst.step sevm devm .staticcall =
      Jaune.XStep.spawn f rsm)
    (sameTarget : f.inner.currentTarget = sevm.currentTarget)
    (notDelegation :
      ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rcases h1 : devm.pop with err | ⟨gas, d1⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Jaune.Xinst.step, hsg, h1, Jaune.XStep.ofExcept] at spawn
  rcases h2 : d1.popToAdr with err | ⟨callee, d2⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Jaune.Xinst.step, hsg, h1, h2, Jaune.XStep.ofExcept] at spawn
  rcases h3 : d2.popToNat with err | ⟨ii, d3⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Jaune.Xinst.step, hsg, h1, h2, h3, Jaune.XStep.ofExcept] at spawn
  rcases h4 : d3.popToNat with err | ⟨isz, d4⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Jaune.Xinst.step, hsg, h1, h2, h3, h4, Jaune.XStep.ofExcept] at spawn
  rcases h5 : d4.popToNat with err | ⟨oi, d5⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Jaune.Xinst.step, hsg, h1, h2, h3, h4, h5, Jaune.XStep.ofExcept] at spawn
  rcases h6 : d5.popToNat with err | ⟨osz, d6⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Jaune.Xinst.step, hsg, h1, h2, h3, h4, h5, h6, Jaune.XStep.ofExcept] at spawn
  have hcode : (addAccessedAddress d6 callee).getCode callee =
      devm.getCode callee := by
    rw [addAccessedAddress_getCode]
    exact (Devm.popToNat_getCode h6).trans
      ((Devm.popToNat_getCode h5).trans
      ((Devm.popToNat_getCode h4).trans
      ((Devm.popToNat_getCode h3).trans
      ((Devm.popToAdr_getCode h2).trans
        (Devm.pop_getCode h1)))))
  simp only [Jaune.Xinst.step, h1, h2, h3, h4, h5, h6,
    Bind.bind, Except.bind] at spawn
  repeat' split at spawn
  all_goals simp only [Jaune.XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | have hf := genericCall.step_spawn_frame spawn
      have hcallee : callee = sevm.currentTarget :=
        hf.2.1.symm.trans sameTarget
      have hnd : ¬ isValidDelegation
          ((addAccessedAddress d6 callee).getCode callee) := by
        rw [hcode, hcallee, ← sameTarget]
        exact notDelegation
      have hdel := Blanc.GasSchedule.accessDelegation_of_not_delegation
        (gas := sevm.benvStat.rules.gas) hnd
      rw [hf.2.2, congrArg (fun t => t.2.2.1) hdel, hcode]
      exact congrArg devm.getCode hf.2.1.symm
    | have hf := genericCallAmsterdam.step_spawn_frame spawn
      have hcallee : callee = sevm.currentTarget :=
        hf.2.1.symm.trans sameTarget
      have hnd : ¬ isValidDelegation
          ((addAccessedAddress d6 callee).getCode callee) := by
        rw [hcode, hcallee, ← sameTarget]
        exact notDelegation
      rw [hf.2.2, Blanc.amsterdamCallCode_of_not_delegation hnd, hcode]
      exact congrArg devm.getCode hf.2.1.symm

end Blanc
