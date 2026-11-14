import Jaune.NativePrecompile
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

theorem staticcall_spawn_not_run_of_precompile {sevm : Sevm} {pre : Devm} {frame : Jaune.Frame}
    {rsm : Resume} {cevm : Evm} {g t ii size oi outSize : B256} {rest : Stack}
    (hstack : pre.stack = g :: t :: ii :: size :: oi :: outSize :: rest)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hpre : decide (sevm.benvStat.rules.isPrecomp t.toAdr) = true)
    (hnodeleg : sevm.benvStat.rules.delegationEnabled = true →
      getDelegatedCodeAddress (pre.getCode t.toAdr) = none)
    (hspawn : Xinst.step sevm pre .staticcall = .spawn frame rsm)
    (henter : frame.enter = .run cevm) : False := by
  have direct : sevm.benvStat.rules.delegatedCodeAddress (pre.getCode t.toAdr) = none := by
    cases enabled : sevm.benvStat.rules.delegationEnabled with
    | false => exact ForkRules.delegatedCodeAddress_disabled enabled _
    | true =>
        rw [ForkRules.delegatedCodeAddress_enabled enabled]
        exact hnodeleg enabled
  exact Jaune.Xinst.step_staticcall_not_run_of_precompile hstack hsg hpre direct hspawn henter

end Blanc.Lift
