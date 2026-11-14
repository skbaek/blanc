import Blanc.Lift.CallCodeResolution
import Blanc.StaticPrecompileMessage

/-! Native STATICCALL observations over the original instruction and frame semantics. -/
namespace Blanc.Lift
open Jaune Blanc

private theorem callCodeH_direct {deleg : Bool} {s : Devm} {t na : Adr}
    {code : ByteArray} {dp : Bool}
    (ready : deleg = true → getDelegatedCodeAddress (s.getCode t) = none)
    (resolved : CallCodeH deleg s t na code dp) : na = t ∧ dp = false := by
  cases deleg with
  | false => exact ⟨resolved.1, resolved.2.2⟩
  | true =>
      have direct := CallCodeH.direct_of_nodeleg (ready rfl) resolved
      exact ⟨direct.1, direct.2.2⟩

theorem staticcall_none_getCode_of_precompile {pc : Nat} {sevm : Sevm} {pre post : Devm}
    {g t ii size oi outSize : B256} {rest : Stack}
    (hstack : pre.stack = g :: t :: ii :: size :: oi :: outSize :: rest)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hpre : decide (sevm.benvStat.rules.isPrecomp t.toAdr) = true)
    (hnodeleg : sevm.benvStat.rules.delegationEnabled = true →
      getDelegatedCodeAddress (pre.getCode t.toAdr) = none)
    (hrun : Ninst.StepRun pc sevm pre (.exec .staticcall) .none (.ok post)) :
    ∀ a, post.getCode a = pre.getCode a := by
  have hp : (g :: t :: ii :: size :: oi :: outSize :: rest) <<+ pre.stack := by
    rw [hstack]
    simpa only [List.append_nil] using
      (pref_append (g :: t :: ii :: size :: oi :: outSize :: rest) [])
  have hfill : Xlot.Filled .none := trivial
  rcases of_step_staticcall_val_with_depth_frame_causeH hp hfill hrun hsg with
    ⟨_, hworld, _⟩ |
    ⟨parent, child, dp, na, code0, avail, _, _, hst, _, _, _, hdel, _, hpm, _, _, hsf, _⟩
  · intro a
    exact (hworld.getCode a).symm
  · have hna := callCodeH_direct hnodeleg hdel
    rcases hna with ⟨rfl, rfl⟩
    intro a
    exact (getCode_eq_of_state_eq hsf a).trans
      ((code_of_processMessage_staticPrecomp hpre hpm a).trans (getCode_eq_of_state_eq hst a))

private theorem genericCall_precompile_not_run
    {sevm : Sevm} {devm : Devm} {target : Adr} {gas ii isz oi osz : Nat} {code0 : ByteArray}
    {frame : Jaune.Frame} {rsm : Resume} {cevm : Evm}
    (hpre : decide (sevm.benvStat.rules.isPrecomp target) = true)
    (hspawn : genericCall.step sevm devm gas 0 sevm.currentTarget target target true true
      ii isz oi osz code0 false = .spawn frame rsm)
    (henter : frame.enter = .run cevm) : False := by
  unfold genericCall.step at hspawn
  split at hspawn
  · simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hspawn
    repeat' split at hspawn
    all_goals simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  · simp only [XStep.spawn.injEq] at hspawn
    obtain ⟨rfl, -⟩ := hspawn
    let cmsg := callMsg sevm (devm.withReturnData []) gas 0 sevm.currentTarget target target true true
      (Array.sliceD devm.memory.data ii isz 0) code0 false
    change (Frame.ofCall cmsg).enter = .run cevm at henter
    unfold Frame.enter at henter
    dsimp only [Frame.ofCall] at henter
    rcases hbt : cmsg.benvAfterTransfer with e | benv <;> rw [hbt] at henter
    · cases henter
    · have hval : cmsg.value = 0 := rfl
      have hbenv := benvAfterTransfer_eq_of_not_transfer (fun h => h.2 hval) hbt
      subst hbenv
      unfold executeCode.enter at henter
      simp only [cmsg, Msg.withBenv, callMsg, Bool.not_false, Bool.true_and, hpre, ↓reduceIte] at henter
      cases henter

theorem staticcall_spawn_not_run_of_precompile {sevm : Sevm} {pre : Devm} {frame : Jaune.Frame}
    {rsm : Resume} {cevm : Evm} {g t ii size oi outSize : B256} {rest : Stack}
    (hstack : pre.stack = g :: t :: ii :: size :: oi :: outSize :: rest)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hpre : decide (sevm.benvStat.rules.isPrecomp t.toAdr) = true)
    (hnodeleg : sevm.benvStat.rules.delegationEnabled = true →
      getDelegatedCodeAddress (pre.getCode t.toAdr) = none)
    (hspawn : Xinst.step sevm pre .staticcall = .spawn frame rsm)
    (henter : frame.enter = .run cevm) : False := by
  have hp : (g :: t :: ii :: size :: oi :: outSize :: rest) <<+ pre.stack := by
    rw [hstack]
    simpa only [List.append_nil] using
      (pref_append (g :: t :: ii :: size :: oi :: outSize :: rest) [])
  simp only [Xinst.step, Bind.bind, Except.bind] at hspawn
  rw [hsg] at hspawn
  rcases eq1 : Devm.pop pre with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨target, devm2⟩ <;> simp only [eq2] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : t = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst x2
  have ht2 : target = t.toAdr := hx2.symm
  subst ht2
  rcases eq3 : Devm.popToNat devm2 with _ | ⟨inputIndex, devm3⟩ <;> simp only [eq3] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f3 := (Devm.pop_of_popToNat_val eq3).choose_spec.1
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputSize, devm4⟩ <;> simp only [eq4] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f4 := (Devm.pop_of_popToNat_val eq4).choose_spec.1
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨outputIndex, devm5⟩ <;> simp only [eq5] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f5 := (Devm.pop_of_popToNat_val eq5).choose_spec.1
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputSize, devm6⟩ <;> simp only [eq6] at hspawn
  · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  have f6 := (Devm.pop_of_popToNat_val eq6).choose_spec.1
  have h_st6 : pre.state = devm6.state :=
    (f1.state).trans ((f2.state).trans ((f3.state).trans
      ((f4.state).trans ((f5.state).trans f6.state))))
  have hdel_solve : ∀ {D D' : Devm} {dp : Bool} {na : Adr} {code0 : ByteArray} {dagc : Nat},
      sevm.benvStat.rules.accessDelegation D t.toAdr = (dp, na, code0, dagc, D') →
      D.state = devm6.state →
      na = t.toAdr ∧ dp = false := by
    intro D D' dp na code0 dagc hp10 hD
    have hdel := callCodeH_of_accessDelegation (hD.trans h_st6.symm) hp10
    exact callCodeH_direct hnodeleg hdel
  rcases hac : sevm.benvStat.rules.access with gflat | _
  swap
  · simp only [hac] at hspawn
    rcases hp10 : sevm.benvStat.rules.accessDelegation (addAccessedAddress devm6 t.toAdr) t.toAdr with
      ⟨dp, na, code0, dagc, devm8⟩
    simp only [hp10] at hspawn
    obtain ⟨rfl, rfl⟩ := hdel_solve hp10 rfl
    split at hspawn
    · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
    simp only [Pure.pure, Except.pure, XStep.ofExcept] at hspawn
    exact genericCall_precompile_not_run hpre hspawn henter
  · simp only [hac] at hspawn
    rcases hp10 : sevm.benvStat.rules.accessDelegation devm6 t.toAdr with ⟨dp, na, code0, dagc, devm8⟩
    simp only [hp10] at hspawn
    obtain ⟨rfl, rfl⟩ := hdel_solve hp10 rfl
    split at hspawn
    · simp only [XStep.ofExcept, reduceCtorEq] at hspawn
    simp only [Pure.pure, Except.pure, XStep.ofExcept] at hspawn
    exact genericCall_precompile_not_run hpre hspawn henter


end Blanc.Lift
