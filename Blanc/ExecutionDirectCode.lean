import Blanc.CommonProofs

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-- Shared tail of the direct-call arms: once the operands are popped, an
undelegated callee's own code is what the child enters. -/
private theorem directCall_tail_code {sevm : Sevm} {devm D : Devm} {f : Frame}
    {callee : Adr}
    (hcode : D.getCode callee = devm.getCode callee)
    (hnd : ¬ isValidDelegation (devm.getCode callee))
    (htarget : f.inner.currentTarget = callee)
    (hcases : f.inner.code = (sevm.benvStat.rules.accessDelegation D callee).2.2.1 ∨
      f.inner.code = (completeDelegationAccess
        (Devm.balReadAccount sevm.benvStat.rules
          (sevm.benvStat.rules.delegationCost D callee).2.1
          (Devm.balReadAccount sevm.benvStat.rules callee D))
        (sevm.benvStat.rules.delegationCost D callee).1
        (sevm.benvStat.rules.delegationCost D callee).2.1).1) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rw [htarget]
  rw [← hcode] at hnd
  rcases hcases with h | h
  · rw [h, congrArg (fun t => t.2.2.1) (ForkRules.accessDelegation_of_not_delegation hnd), hcode]
  · rw [h, amsterdamCallCode_of_not_delegation hnd, hcode]

theorem Xinst.step_call_spawn_code {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume}
    (spawn : Xinst.step sevm devm .call = .spawn f rsm)
    (notDelegation : ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rcases h1 : devm.pop with err | ⟨gas, d1⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, ne_eq, Bool.decide_and, decide_not, Except.bind_ok] at spawn
  rcases h2 : d1.popToAdr with err | ⟨callee, d2⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, Except.bind_ok, h2, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, ne_eq, Bool.decide_and, decide_not] at spawn
  rcases h3 : d2.pop with err | ⟨value, d3⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, Except.bind_ok, h2, h3, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, ne_eq, Bool.decide_and, decide_not] at spawn
  rcases h4 : d3.popToNat with err | ⟨ii, d4⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, Except.bind_ok, h2, h3, h4, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, ne_eq, Bool.decide_and, decide_not] at spawn
  rcases h5 : d4.popToNat with err | ⟨isz, d5⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, Except.bind_ok, h2, h3, h4, h5, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, ne_eq, Bool.decide_and, decide_not] at spawn
  rcases h6 : d5.popToNat with err | ⟨oi, d6⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, Except.bind_ok, h2, h3, h4, h5, h6, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, ne_eq, Bool.decide_and, decide_not] at spawn
  rcases h7 : d6.popToNat with err | ⟨osz, d7⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, Except.bind_ok, h2, h3, h4, h5, h6, h7, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, ne_eq, Bool.decide_and, decide_not] at spawn
  have hcode : (addAccessedAddress d7 callee).getCode callee = devm.getCode callee := by
    rw [addAccessedAddress_getCode, Devm.popToNat_getCode h7, Devm.popToNat_getCode h6,
      Devm.popToNat_getCode h5, Devm.popToNat_getCode h4, Devm.pop_getCode h3,
      Devm.popToAdr_getCode h2, Devm.pop_getCode h1]
  have hcode0 : d7.getCode callee = devm.getCode callee := by
    rw [← hcode, addAccessedAddress_getCode]
  simp only [Xinst.step, h1, h2, h3, h4, h5, h6, h7, Bind.bind, Except.bind,
    Except.assert, Pure.pure, Except.pure] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | have hf := genericCall.step_spawn_frame spawn
      first
        | exact directCall_tail_code hcode (by rw [← hf.2.1]; exact notDelegation) hf.2.1
            (Or.inl hf.2.2)
        | exact directCall_tail_code hcode0 (by rw [← hf.2.1]; exact notDelegation) hf.2.1
            (Or.inl hf.2.2)
    | have hf := genericCallAmsterdam.step_spawn_frame spawn
      exact directCall_tail_code hcode (by rw [← hf.2.1]; exact notDelegation) hf.2.1
        (Or.inr hf.2.2)

theorem Xinst.step_staticcall_spawn_code {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume}
    (spawn : Xinst.step sevm devm .staticcall = .spawn f rsm)
    (notDelegation : ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rcases h1 : devm.pop with err | ⟨gas, d1⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, add_zero] at spawn
  rcases h2 : d1.popToAdr with err | ⟨callee, d2⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, Except.bind_error, reduceCtorEq, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft, add_zero] at spawn
  rcases h3 : d2.popToNat with err | ⟨ii, d3⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, h3, Except.bind_error, reduceCtorEq, add_zero, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft] at spawn
  rcases h4 : d3.popToNat with err | ⟨isz, d4⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, h3, h4, Except.bind_error, reduceCtorEq, add_zero, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft] at spawn
  rcases h5 : d4.popToNat with err | ⟨oi, d5⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, h3, h4, h5, Except.bind_error, reduceCtorEq, add_zero, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft] at spawn
  rcases h6 : d5.popToNat with err | ⟨osz, d6⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp only [Xinst.step, hsg, XStep.ofExcept, h1, bind_pure_comp, Except.bind_ok, h2, h3, h4, h5, h6, Except.bind_error, reduceCtorEq, add_zero, Devm.balReadAccount_gasLeft, addAccessedAddress_gasLeft] at spawn
  have hcode : (addAccessedAddress d6 callee).getCode callee = devm.getCode callee := by
    rw [addAccessedAddress_getCode, Devm.popToNat_getCode h6, Devm.popToNat_getCode h5,
      Devm.popToNat_getCode h4, Devm.popToNat_getCode h3,
      Devm.popToAdr_getCode h2, Devm.pop_getCode h1]
  have hcode0 : d6.getCode callee = devm.getCode callee := by
    rw [← hcode, addAccessedAddress_getCode]
  simp only [Xinst.step, h1, h2, h3, h4, h5, h6, Bind.bind, Except.bind,
    Except.assert, Pure.pure, Except.pure] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | have hf := genericCall.step_spawn_frame spawn
      first
        | exact directCall_tail_code hcode (by rw [← hf.2.1]; exact notDelegation) hf.2.1
            (Or.inl hf.2.2)
        | exact directCall_tail_code hcode0 (by rw [← hf.2.1]; exact notDelegation) hf.2.1
            (Or.inl hf.2.2)
    | have hf := genericCallAmsterdam.step_spawn_frame spawn
      exact directCall_tail_code hcode (by rw [← hf.2.1]; exact notDelegation) hf.2.1
        (Or.inr hf.2.2)

/-- `CALL` and `STATICCALL` enter the callee's own code when the callee carries
no EIP-7702 designator, including a call back into the current account. -/
theorem Xinst.step_directCall_spawn_code {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (direct : x = .call ∨ x = .staticcall)
    (spawn : Xinst.step sevm devm x = .spawn f rsm)
    (notDelegation : ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rcases direct with rfl | rfl
  · exact Xinst.step_call_spawn_code spawn notDelegation
  · exact Xinst.step_staticcall_spawn_code spawn notDelegation

/-- STATICCALL has the same direct-code property as CALL. -/
theorem Xinst.step_staticcall_sameTarget_code
    {sevm : Sevm} {devm : Devm} {f : Jaune.Frame} {rsm : Resume}
    (spawn : Jaune.Xinst.step sevm devm .staticcall =
      Jaune.XStep.spawn f rsm)
    (_sameTarget : f.inner.currentTarget = sevm.currentTarget)
    (notDelegation :
      ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget :=
  Xinst.step_staticcall_spawn_code spawn notDelegation

/-- A direct CALL back into the current target loads that target's own code
when the installed account is not an EOA delegation designator. -/
theorem Xinst.step_call_sameTarget_code
    {sevm : Sevm} {devm : Devm} {f : Jaune.Frame} {rsm : Resume}
    (spawn : Jaune.Xinst.step sevm devm .call = Jaune.XStep.spawn f rsm)
    (_sameTarget : f.inner.currentTarget = sevm.currentTarget)
    (notDelegation :
      ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget :=
  Xinst.step_call_spawn_code spawn notDelegation

end Blanc
