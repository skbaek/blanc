import Blanc.OwnerDiscipline
import Blanc.OwnerClosure
import Blanc.Lift.InvWalkWorld

/-!
# The exact child of a spawning `DELEGATECALL` (contract-neutral)

`Xinst.step_delegatecall_spawn_exact`: a `DELEGATECALL` step that spawns, on a covered fork, whose
code-address operand `w` names an undelegated account, enters a child message at the parent's
storage owner with code address `w`, the parent's caller, value and static flag, `w`'s code, and
the calldata the input window of the parent's (extended) memory holds.  A hoist candidate for
`Blanc/DelegatecallEnvelope.lean`.
-/

namespace Blanc

open Jaune

theorem Xinst.step_delegatecall_spawn_exact {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {g w : B256} {s : List B256}
    (hfork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm devm .delegatecall = .spawn f rsm)
    (hstack : devm.stack = g :: w :: s)
    (undelegated : getDelegatedCodeAddress (devm.getCode w.toAdr) = none) :
    f.inner.currentTarget = sevm.currentTarget ∧ f.inner.codeAddress = w.toAdr ∧
      f.inner.caller = sevm.caller ∧ f.inner.value = sevm.value ∧
      f.inner.isStatic = sevm.isStatic ∧ f.inner.code = devm.getCode w.toAdr ∧
      ∃ (ii is oi os : B256) (s' : List B256), s = ii :: is :: oi :: os :: s' ∧
        f.inner.data = (devm.memory.read ii.toNat is.toNat).1 := by
  have hx := spawn
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  rw [hsg] at hx
  have hp : (g :: w :: s) <<+ devm.stack := by
    rw [hstack]
    simpa only [List.append_nil] using (pref_append (g :: w :: s) [])
  rcases eq1 : Devm.pop devm with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;> simp only [eq2] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : w = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst hv2
  subst hx2
  replace hp := cons_pref_cons_inv hp
  rcases eq4 : Devm.popToNat devm2 with _ | ⟨inputIndex, devm4⟩ <;> simp only [eq4] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
  have e4 := f4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;> simp only [eq5] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
  have e5 := f5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;> simp only [eq6] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;> simp only [eq7] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq7 with ⟨x7, f7, hk7⟩
  have e7 := f7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e7
  subst hk4 hk5 hk6 hk7
  have hs : s = x4 :: x5 :: x6 :: x7 :: devm7.stack := by
    have := hstack.symm.trans (by rw [e1, e2, e4, e5, e6, e7])
    simp only [List.cons.injEq] at this
    exact this.2.2
  have h_st7 : devm.state = devm7.state :=
    (f1.state).trans ((f2.state).trans ((f4.state).trans ((f5.state).trans
      ((f6.state).trans f7.state))))
  have h_mem7 : devm.memory = devm7.memory :=
    (f1.memory).trans ((f2.memory).trans ((f4.memory).trans ((f5.memory).trans
      ((f6.memory).trans f7.memory))))
  clear e1 e2 e4 e5 e6 e7 f1 f2 f4 f5 f6 f7 eq1 eq2 eq4 eq5 eq6 eq7 h_pop2 hp
  rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress devm7 w.toAdr) w.toAdr with ⟨dp, na, code0, dagc, devm9⟩
  simp only [hp11] at hx
  have h_gc7 : (addAccessedAddress devm7 w.toAdr).state.getCode w.toAdr =
      devm.getCode w.toAdr := by
    show devm7.state.getCode w.toAdr = devm.getCode w.toAdr
    rw [← h_st7]
    rfl
  have h_del : na = w.toAdr ∧ code0 = devm.getCode w.toAdr := by
    have h_acc := hp11
    dsimp only [GasSchedule.accessDelegation] at h_acc
    rw [h_gc7, undelegated] at h_acc
    simp only [Prod.mk.injEq] at h_acc
    exact ⟨h_acc.2.1.symm, h_acc.2.2.1.symm⟩
  obtain ⟨rfl, rfl⟩ := h_del
  have h_mem9 : devm9.memory = devm7.memory := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).memory) hp11
    dsimp only at h
    rw [← h, GasSchedule.accessDelegation_memory]
    rfl
  split at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rename_i devm10 eq16
  have h_mem10 : devm9.memory = devm10.memory := (Devm.burn_of_chargeGas eq16).memory
  simp only [Pure.pure, Except.pure, XStep.ofExcept] at hx
  obtain ⟨hf, -⟩ := genericCall_step_spawn_exact hx
  subst hf
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, x4, x5, x6, x7, devm7.stack, hs, ?_⟩
  · simp only [Frame.ofCall, callMsg, Bool.false_or]
  · show ((devm10.memory.extends [(x4.toNat, x5.toNat), (x6.toNat, x7.toNat)]).read
      x4.toNat x5.toNat).1 = _
    rw [← h_mem10, h_mem9, ← h_mem7]
    rfl

/-- A spawning `DELEGATECALL` runs at a nonzero depth, enters a call frame one level deeper, and
resumes as a call. -/
theorem Xinst.step_delegatecall_spawn_meta {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume}
    (hfork : CoveredFork sevm.benvStat.fork)
    (spawn : Xinst.step sevm devm .delegatecall = .spawn f rsm) :
    sevm.depth ≠ 0 ∧ f.inner.depth = sevm.depth - 1 ∧ f.isCreate = false ∧
      ∃ (parent : Devm) (oi os : Nat), rsm = .call parent oi os := by
  have hx := spawn
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hfork.rules_stateGas_none] at hx
  dsimp only at hx
  repeat' split at hx
  all_goals simp only [XStep.ofExcept, reduceCtorEq, Pure.pure, Except.pure] at hx
  all_goals first
    | cases hx
    | (have hd : sevm.depth ≠ 0 := by
          intro h0
          simp only [genericCall.step, h0, ↓reduceIte] at hx
          revert hx
          simp only [XStep.ofExcept, Bind.bind, Except.bind, Pure.pure, Except.pure]
          split
          · simp only [reduceCtorEq, imp_false, not_false_eq_true]
          · rename_i hm
            intro hs
            subst hs
            split at hm <;> simp only [reduceCtorEq, Except.ok.injEq] at hm
       obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact hx
       exact ⟨hd, rfl, rfl, _, _, _, rfl⟩)

/-- A `DELEGATECALL` that completes without a child frame pushes the failure flag `0`. -/
theorem Xinst.step_delegatecall_done_flag {sevm : Sevm} {devm d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (done : Xinst.step sevm devm .delegatecall = .done (.ok d)) :
    ∃ s, d.stack = 0 :: s := by
  have hx := done
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  rw [hfork.rules_stateGas_none] at hx
  dsimp only at hx
  repeat' split at hx
  all_goals simp only [XStep.ofExcept, reduceCtorEq, Pure.pure, Except.pure] at hx
  all_goals first
    | cases hx
    | (simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at hx
       repeat' split at hx
       all_goals simp only [XStep.ofExcept, reduceCtorEq, XStep.done.injEq, Except.ok.injEq] at hx
       all_goals subst hx
       rename_i pushed pushEq
       exact ⟨_, (Devm.push_of_push pushEq).stack⟩)

/-- **Resuming a call frame.**  The parent resumes with the success flag `1`, the child's output as
returndata and the child's world when the child's raw run succeeded cleanly; otherwise with the
flag `0`. -/
theorem Resume.call_run_inv {parent : Devm} {oi os : Nat} {f : Frame} {raw : Execution} {d : Devm}
    (hf : f.isCreate = false) (hsg : f.inner.benv.stat.rules.stateGas = none)
    (h : Resume.run (.call parent oi os) (f.settle raw) = .ok d) :
    (∃ x, raw = .ok x ∧ x.error = none ∧ (∃ s, d.stack = 1 :: s) ∧ d.state = x.state ∧
      d.returnData = x.output) ∨ ∃ s, d.stack = 0 :: s := by
  unfold Frame.settle Frame.settleMsg at h
  rw [hsg, hf] at h
  simp only [executeCode.handleErrorWith, Bool.false_eq_true, ↓reduceIte] at h
  -- the flag pushed by the resumption
  have flag : ∀ {y : Devm}, Resume.run (.call parent oi os) (.ok y) = .ok d →
      (y.error = none ∧ (∃ s, d.stack = 1 :: s) ∧ d.state = y.state ∧ d.returnData = y.output) ∨
        ∃ s, d.stack = 0 :: s := by
    intro y hy
    unfold Resume.run liftToExecution at hy
    simp only [bind, Except.bind] at hy
    cases hey : y.error with
    | some e =>
        right
        simp only [hey, Option.isSome_some, ↓reduceIte] at hy
        rcases hp : (incorporateChildOnError parent y y.output).push 0 with _ | d' <;>
          rw [hp] at hy
        · cases hy
        · injection hy with hy
          subst hy
          have := Blanc.Lift.Devm.eq_of_push_ok hp
          subst this
          exact ⟨_, rfl⟩
    | none =>
        left
        simp only [hey, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hy
        rcases hp : (incorporateChildOnSuccess parent y y.output).push 1 with _ | d' <;>
          rw [hp] at hy
        · cases hy
        · injection hy with hy
          subst hy
          have := Blanc.Lift.Devm.eq_of_push_ok hp
          subst this
          exact ⟨rfl, ⟨_, rfl⟩, rfl, rfl⟩
  have settledErr : ∀ {y : Devm}, y.error.isSome = true →
      ∀ (w : State) (t : Tra) (k : KeySet),
        Resume.run (.call parent oi os) (.ok ((y.rollback w t).withStorageWrites k)) = .ok d →
        ∃ s, d.stack = 0 :: s := by
    intro y hy w t k hr
    rcases flag hr with ⟨hn, -⟩ | h0
    · have : ((y.rollback w t).withStorageWrites k).error = y.error := rfl
      rw [this] at hn
      rw [hn] at hy
      cases hy
    · exact h0
  rcases raw with ⟨e, evm⟩ | x
  · right
    rcases e with r | _ | r | r <;>
      simp only [executeCode.handleError, processMessage.settle, bind, Except.bind] at h
    · split at h
      · exact settledErr rfl _ _ _ h
      · rename_i hn
        exact absurd rfl hn
    · split at h
      · exact settledErr rfl _ _ _ h
      · rename_i hn
        exact absurd rfl hn
    · simp only [Resume.run, liftToExecution, bind, Except.bind, reduceCtorEq] at h
    · simp only [Resume.run, liftToExecution, bind, Except.bind, reduceCtorEq] at h
  · simp only [executeCode.handleError, processMessage.settle, bind, Except.bind] at h
    split at h
    · rename_i hx
      exact .inr (settledErr hx _ _ _ h)
    · rcases flag h with ⟨hn, rest⟩ | h0
      · exact .inl ⟨x, rfl, hn, rest⟩
      · exact .inr h0

end Blanc
