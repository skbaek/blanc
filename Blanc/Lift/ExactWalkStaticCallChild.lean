import Blanc.Lift.ExactWalkCallChild

/-!
The known clean-child STATICCALL crossing, retaining the actual fork,
delegation/access, gas, depth, stack-room and entered child execution premises.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- A `STATICCALL` to a non-precompile callee whose entered child halts cleanly resumes in
`callChildPost`.  The static sibling of `Ninst.runCompiled_call_zero_child`. -/
lemma Ninst.runCompiled_staticcall_child {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_room : s.length < 1024)
    (h_exec : exec (initEvm (staticcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs tw.toAdr dadr iiw.toNat isw.toNat code dp)) = .ok cpost)
    (h_error : cpost.error = none) :
    Ninst.RunCompiled sevm devm (.exec .staticcall)
      (callChildPost (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
        cpost oiw.toNat osw.toNat) := by
  let p := callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := staticcallSpawnMsg sevm p mcs tw.toAdr dadr iiw.toNat isw.toNat code dp
  have hbt : msg.benvAfterTransfer = .ok msg.benv :=
    Msg.benvAfterTransfer_of_value_zero rfl
  let child := initEvm (msg.withBenv msg.benv)
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have hexec : exec child = .ok cpost := by
    simpa only [child, msg, p, staticcallSpawnMsg, callMsg, Msg.withBenv] using h_exec
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok cpost := by
    rw [hexec, Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
    have hsweep : msg.benv.stat.rules.settle.touchedSweep = false :=
      CoveredFork.rules_touchedSweep (s := sevm.benvStat) hfork
    simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, h_error,
      Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
      Devm.recordTouch_of_not_touchedSweep hsweep]
  have hdi := accessDelegation_inv h_del
  have hpstack : p.stack.length < 1024 := by
    change d1.stack.length < 1024
    rw [hdi.1]
    exact h_room
  have hres : Resume.run (.call p oiw.toNat osw.toNat)
      ((Frame.ofCall msg).settle (exec child)) =
        .ok (callChildPost p cpost oiw.toNat osw.toNat) := by
    rw [hsettle, Resume.run_call_ok (by rw [h_error]; rfl) hpstack]
    rfl
  exact Ninst.runCompiled_exec_run
    (Xinst.step_staticcall_spawn hfork h_stk h_ext h_del h_acc h_split h_gas h_depth) henter hres

end Blanc.Lift
