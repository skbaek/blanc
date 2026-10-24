import Blanc.Lift.Usdc.ProxyCreation.Effects
import Blanc.Lift.Usdc.ProxyCreation.RuntimeWindow
import Blanc.DeploymentTouch
import Blanc.Lift.Usdc.ProxyCreation.HistoryFrame
import Blanc.MessageExecutionInversion

/-!
# Constructor-to-CREATE zero-row composition for the original proxy constructor

One bounded concrete local composition from the existing source effects and
actual forward touch/charge settlement: a demanded row distinct from both
literal constructor slots is zero in the actual installed CREATE result.
Historical lifting, occurrence, admission, replay, and transaction cuts remain
separate obligations.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune

/-- One constructor-to-CREATE zero-row composition at the actual entry:
the actual transfer, the actual execution of the actual entry machine to the
actual raw result, and the actual touch/charge settlement install a result
whose protected row at the target is zero. -/
theorem constructor_message_zero
    {msg : Msg} {benv : Benv} {raw charged : Devm} {key : B256}
    (hcode : msg.code = code)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = none)
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hexec : exec (initEvm ((processCreateMessage.msg msg).withBenv benv)) = .ok raw)
    (herror : raw.error = none)
    (hcharge : processCreateMessage.chargeCodeGas msg.benv.stat.rules
      (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget raw) = .ok charged)
    (hrun : SFunc.Run cert.prog
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna
      t_0000_c0 (.halted raw))
    (himpl : key ≠ implSlot)
    (hadmin : key ≠ adminSlot) :
    ∃ installed, processCreateMessage msg = .ok installed ∧
      installed.getStorVal msg.currentTarget key = 0 := by
  have hsevm_code :
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta.code = code :=
    hcode
  have hzero : (processCreateMessage.msg msg).value = 0 := hvalue
  have hrunSt : SFunc.Run cert.prog
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
      (St (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna [] Mem.empty
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna.gasLeft)
      t_0000_c0 (.halted raw) := hrun
  have hbenv_stor : benv.state.getStor msg.currentTarget = Stor.empty := by
    have hkeep :=
      benvAfterTransfer_ok_getStor htransfer msg.currentTarget (Or.inl hzero)
    rw [hkeep]
    exact processCreateMessage_msg_getStor_currentTarget msg
  have hbase :
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna.getStorVal
        msg.currentTarget key = 0 := by
    show (benv.state.getStor msg.currentTarget).get key = 0
    rw [hbenv_stor]
    simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
      Std.TreeMap.getD_emptyc]
  have hraw : raw.getStorVal msg.currentTarget key = 0 :=
    (constructor_row_preserved hsevm_code hrunSt himpl hadmin).trans hbase
  have htouched : (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget
      raw).getStorVal msg.currentTarget key = 0 := by
    have hg : Devm.getStor (Devm.recordTouch msg.benv.stat.rules true
        msg.currentTarget raw) msg.currentTarget =
        Devm.getStor raw msg.currentTarget := by
      show (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget
        raw).state.getStor msg.currentTarget =
        raw.state.getStor msg.currentTarget
      rw [Devm.recordTouch_state]
    exact (congrArg (fun s => s.get key) hg).trans hraw
  have hcharged : charged.getStorVal msg.currentTarget key = 0 := by
    have hstate := chargeCodeGas_state_ok hcharge
    have hg : Devm.getStor charged msg.currentTarget =
        Devm.getStor (Devm.recordTouch msg.benv.stat.rules true
          msg.currentTarget raw) msg.currentTarget := by
      show charged.state.getStor msg.currentTarget =
        (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget
          raw).state.getStor msg.currentTarget
      rw [hstate]
    exact (congrArg (fun s => s.get key) hg).trans htouched
  have hsettle : processCreateMessage msg =
      .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩) :=
    processCreateMessage_ok_touch_of_exec_and_charge msg htransfer hcodeAddress
      hexec herror hcharge
  refine ⟨_, hsettle, ?_⟩
  show (((charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩).getStor
    msg.currentTarget).get key) = 0
  simp only [Devm.setCode_getStor]
  split
  · simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
      Std.TreeMap.getD_emptyc]
  · exact hcharged

/-- One constructor-to-CREATE installed-code composition at the actual entry:
the actual transfer, the actual execution of the actual entry machine to the
actual raw result, and the actual touch/charge settlement install a result
whose target carries the registered proxy runtime and the exact whole target
storage. -/
theorem constructor_message_effects
    {msg : Msg} {benv : Benv} {raw charged : Devm}
    (hcode : msg.code = code)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = none)
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hexec : exec (initEvm ((processCreateMessage.msg msg).withBenv benv)) = .ok raw)
    (herror : raw.error = none)
    (hcharge : processCreateMessage.chargeCodeGas msg.benv.stat.rules
      (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget raw) = .ok charged)
    (hrun : SFunc.Run cert.prog
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna
      t_0000_c0 (.halted raw)) :
    ∃ installed, processCreateMessage msg = .ok installed ∧
      installed.getCode msg.currentTarget = Proxy.code ∧
      installed.getStor msg.currentTarget =
        (Stor.empty.set implSlot initialImplementation).set adminSlot
          msg.caller.toB256 := by
  have hsevm_code :
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta.code = code :=
    hcode
  have hzero : (processCreateMessage.msg msg).value = 0 := hvalue
  have hrunSt : SFunc.Run cert.prog
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
      (St (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna [] Mem.empty
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna.gasLeft)
      t_0000_c0 (.halted raw) := hrun
  have hbenv_stor : benv.state.getStor msg.currentTarget = Stor.empty := by
    have hkeep :=
      benvAfterTransfer_ok_getStor htransfer msg.currentTarget (Or.inl hzero)
    rw [hkeep]
    exact processCreateMessage_msg_getStor_currentTarget msg
  obtain ⟨hstor, houtput, -⟩ := constructor_effects_of_run hsevm_code hrunSt
  have hraw_stor : raw.getStor msg.currentTarget =
      (Stor.empty.set implSlot initialImplementation).set adminSlot
        msg.caller.toB256 := by
    have h : raw.getStor msg.currentTarget =
        (((benv.state.getStor msg.currentTarget).set implSlot
          initialImplementation).set adminSlot msg.caller.toB256) := hstor
    rw [hbenv_stor] at h
    exact h
  have hraw_out : raw.output = Proxy.code.toList := by
    rw [houtput]
    exact runtime_window
  have hcharged_stor : charged.getStor msg.currentTarget =
      raw.getStor msg.currentTarget := by
    have hstate := chargeCodeGas_state_ok hcharge
    have hg : Devm.getStor charged msg.currentTarget =
        Devm.getStor (Devm.recordTouch msg.benv.stat.rules true
          msg.currentTarget raw) msg.currentTarget := by
      show charged.state.getStor msg.currentTarget =
        (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget
          raw).state.getStor msg.currentTarget
      rw [hstate]
    rw [hg]
    show Devm.getStor (Devm.recordTouch msg.benv.stat.rules true
      msg.currentTarget raw) msg.currentTarget =
      Devm.getStor raw msg.currentTarget
    show (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget
      raw).state.getStor msg.currentTarget =
      raw.state.getStor msg.currentTarget
    rw [Devm.recordTouch_state]
  have hcharged_out : charged.output = raw.output := by
    have hmach := processCreateMessage.chargeCodeGas_ok_eq_setMach hcharge
    rw [hmach]
    show (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget
      raw).output = raw.output
    exact Devm.recordTouch_output _ _ _ _
  have hout_len : charged.output.length = 2186 := by
    rw [hcharged_out, houtput]
    exact List.length_sliceD _ _ _ _
  have hcode_eq : (⟨⟨charged.output⟩⟩ : ByteArray) = Proxy.code := by
    apply ByteArray.ext
    rw [← Array.toList_inj]
    have e1 : ({data := { toList := charged.output } } : ByteArray).data.toList =
        charged.output := rfl
    have e2 : Proxy.code.data.toList = Proxy.code.toList :=
      ByteArray.toList_eq_toList_data.symm
    rw [e1, e2, hcharged_out, hraw_out]
  have hnotEmpty : ¬ ({charged.state.get msg.currentTarget with code :=
      ⟨⟨charged.output⟩⟩} : Acct).Empty := by
    intro hempty
    have hsize : (⟨⟨charged.output⟩⟩ : ByteArray).size = 0 := hempty.1
    have hsize_eq : (⟨⟨charged.output⟩⟩ : ByteArray).size =
      charged.output.length := rfl
    rw [hsize_eq, hout_len] at hsize
    exact (by decide : 2186 ≠ 0) hsize
  have hinstalled_code : (charged.setCode msg.currentTarget
      ⟨⟨charged.output⟩⟩).getCode msg.currentTarget = Proxy.code := by
    have hget : (charged.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).state.getCode msg.currentTarget =
        ⟨⟨charged.output⟩⟩ := by
      show (charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).getCode msg.currentTarget = ⟨⟨charged.output⟩⟩
      simp only [State.setCode, State.getCode, State.setAccount_get_self,
        Acct.clearIfEmpty_code]
    rw [Devm.getCode_state, hget]
    exact hcode_eq
  have hinstalled_stor : (charged.setCode msg.currentTarget
      ⟨⟨charged.output⟩⟩).getStor msg.currentTarget =
      (Stor.empty.set implSlot initialImplementation).set adminSlot
        msg.caller.toB256 := by
    simp only [Devm.setCode_getStor]
    split
    · next h => exact absurd h.2 hnotEmpty
    · next _ => exact hcharged_stor.trans hraw_stor
  have hsettle : processCreateMessage msg =
      .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩) :=
    processCreateMessage_ok_touch_of_exec_and_charge msg htransfer hcodeAddress
      hexec herror hcharge
  exact ⟨_, hsettle, hinstalled_code, hinstalled_stor⟩

/-- A clean retained CREATE of the registered constructor installs the proxy
runtime and its two initialized slots in that trace's actual result. -/
theorem constructor_effects_of_createTrace
    {msg : Msg} {installed : Devm}
    (trace : Blanc.ExecutionTrace.ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false)
    (hcode : msg.code = code)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = none)
    (hstateGas : msg.benv.stat.rules.stateGas = none) :
    installed.getCode msg.currentTarget = Proxy.code ∧
    installed.getStor msg.currentTarget =
      (Stor.empty.set implSlot initialImplementation).set adminSlot
        msg.caller.toB256 := by
  have actual := trace.result
  rcases trace with ⟨slot, retained, process⟩
  obtain ⟨inner, charged, innerProcess, innerClean, charge, -⟩ :=
    ProcessCreateMessage.ok_charge_of_clean process clean
  have innerResult : processMessage (processCreateMessage.msg msg) = .ok inner :=
    (show Blanc.ExecutionTrace.ProcessMessageTrace
      (processCreateMessage.msg msg) (.ok inner) from ⟨slot, retained, innerProcess⟩).result
  obtain ⟨benv, transfer⟩ := benvAfterTransfer_exists_zero
    (msg := processCreateMessage.msg msg) (show (processCreateMessage.msg msg).value = 0 from hvalue)
  have entry : (Frame.ofCall (processCreateMessage.msg msg)).enter =
      .run (initEvm ((processCreateMessage.msg msg).withBenv benv)) := by
    unfold Frame.enter Frame.ofCall
    rw [transfer]
    have entryCode : (processCreateMessage.msg msg).codeAddress = none := hcodeAddress
    unfold executeCode.enter
    simp only [Msg.withBenv, entryCode]
  have entered := innerProcess
  change RunFrame (Frame.ofCall (processCreateMessage.msg msg)) slot (.ok inner) at entered
  unfold RunFrame at entered
  rw [entry] at entered
  obtain ⟨raw, slotEq, -⟩ := entered
  subst slot
  cases retained with
  | some run =>
      obtain ⟨rawPost, rawEq, rawClean, -, -⟩ :=
        Blanc.MessageExecution.processMessage_clean_rawPost innerProcess innerClean
      subst raw
      have hexec : exec (initEvm ((processCreateMessage.msg msg).withBenv benv)) =
          .ok rawPost := (exec_iff_exec_eq _ _ _ _).mp ⟨run⟩
      have hsg :
          (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta.benvStat.rules.stateGas =
            none := by
        change benv.stat.rules.stateGas = none
        rw [Msg.benvAfterTransfer_ok_stateGas transfer]
        exact hstateGas
      have source := constructor_run_of_exec run
        (show (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta.code = code from hcode)
        hsg rfl rfl
      have touched : inner =
          Devm.recordTouch msg.benv.stat.rules true msg.currentTarget rawPost :=
        Except.ok.inj (innerResult.symm.trans
          (processMessage_ok_touch_of_exec transfer hcodeAddress hexec rawClean))
      rw [touched] at charge
      obtain ⟨result, resultEq, effects⟩ :=
        constructor_message_effects hcode hvalue hcodeAddress transfer hexec rawClean charge source
      have same : installed = result := Except.ok.inj (actual.symm.trans resultEq)
      simpa only [same] using effects

/-- Every row apart from the constructor's two literal slots is zero in the
same clean retained CREATE result. -/
theorem constructor_zero_of_createTrace
    {msg : Msg} {installed : Devm} {key : B256}
    (trace : Blanc.ExecutionTrace.ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false)
    (hcode : msg.code = code)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = none)
    (hstateGas : msg.benv.stat.rules.stateGas = none)
    (himpl : key ≠ implSlot) (hadmin : key ≠ adminSlot) :
    installed.getStorVal msg.currentTarget key = 0 := by
  change (installed.getStor msg.currentTarget).get key = 0
  rw [(constructor_effects_of_createTrace trace clean hcode hvalue hcodeAddress hstateGas).2,
    Stor.get_set_ne _ hadmin.symm, Stor.get_set_ne _ himpl.symm]
  simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc, Std.TreeMap.getD_emptyc]

end Blanc.Lift.Usdc.ProxyCreation
