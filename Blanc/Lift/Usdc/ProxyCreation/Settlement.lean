import Blanc.Lift.Usdc.ProxyCreation.Effects
import Blanc.DeploymentTouch

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

end Blanc.Lift.Usdc.ProxyCreation
