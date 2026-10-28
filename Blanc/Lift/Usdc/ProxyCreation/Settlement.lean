import Blanc.Lift.Usdc.ProxyCreation.Effects
import Blanc.Lift.Usdc.ProxyCreation.RuntimeWindow
import Blanc.DeploymentTouch
import Blanc.Lift.Usdc.ProxyCreation.HistoryFrame
import Blanc.MessageExecutionInversion
import Blanc.Lift.BalSilent

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
  have nonempty : raw.output ≠ [] := by
    intro empty
    have length : raw.output.length = 2186 := by
      rw [houtput]
      exact List.length_sliceD _ _ _ _
    rw [empty, List.length_nil] at length
    cases length
  obtain ⟨installed, settled, code, storage⟩ :=
    processCreateMessage_effects_of_exec_and_charge msg htransfer hcodeAddress
      hexec herror hcharge nonempty
  refine ⟨installed, settled, ?_, ?_⟩
  · rw [code]
    apply ByteArray.ext
    rw [← Array.toList_inj]
    change raw.output = Proxy.code.data.toList
    rw [← ByteArray.toList_eq_toList_data]
    exact hraw_out
  · rw [storage]
    exact hraw_stor

/-- The actual clean retained CREATE supplies the constructor source run and
its exact touch, charge and code-installation result. -/
theorem constructor_witness_of_createTrace
    {msg : Msg} {installed : Devm}
    (trace : Blanc.ExecutionTrace.ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false)
    (hcode : msg.code = code) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = none)
    (hstateGas : msg.benv.stat.rules.stateGas = none) :
    ∃ (benv : Benv) (raw charged : Devm),
      (processCreateMessage.msg msg).benvAfterTransfer = .ok benv ∧
      exec (initEvm ((processCreateMessage.msg msg).withBenv benv)) = .ok raw ∧
      raw.error = none ∧
      processCreateMessage.chargeCodeGas msg.benv.stat.rules
        (Devm.recordTouch msg.benv.stat.rules true msg.currentTarget raw) = .ok charged ∧
      SFunc.Run cert.prog
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna
        t_0000_c0 (.halted raw) ∧
      installed = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩ := by
  -- The legacy value premise remains in the compatibility statement.
  exact createTrace_source_witness cert_check hcode rfl trace clean hcodeAddress hstateGas

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
  obtain ⟨benv, raw, charged, transfer, execRun, rawClean, charge, source, _⟩ :=
    constructor_witness_of_createTrace trace clean hcode hvalue hcodeAddress hstateGas
  obtain ⟨result, resultEq, effects⟩ :=
    constructor_message_effects hcode hvalue hcodeAddress transfer execRun rawClean charge source
  have same : installed = result := Except.ok.inj (trace.result.symm.trans resultEq)
  simpa only [same] using effects

/-- The actual constructor has no external calls or SELFDESTRUCT, so a clean
CREATE preserves exactly the message's inherited deletion set. -/
theorem constructor_deletions_of_createTrace
    {msg : Msg} {installed : Devm}
    (trace : Blanc.ExecutionTrace.ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false)
    (hcode : msg.code = code) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = none)
    (hstateGas : msg.benv.stat.rules.stateGas = none) :
    installed.accountsToDelete = msg.inheritedDeletions := by
  obtain ⟨benv, raw, charged, transfer, execRun, rawClean, charge, source, installedEq⟩ :=
    constructor_witness_of_createTrace trace clean hcode hvalue hcodeAddress hstateGas
  have frame := SFunc.RunP.balance_deletion_frame_of_balSilent (fun h => h)
    (S := [0, 1, 2, 3, 4]) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) source
  have rawDeletion : raw.accountsToDelete = msg.inheritedDeletions :=
    congrArg (fun p => p.2.1) frame
  have chargedDeletion := congrArg Prod.fst (chargeCodeGas_delSets_ok charge)
  rw [installedEq]
  change charged.accountsToDelete = msg.inheritedDeletions
  exact chargedDeletion.trans rawDeletion

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
