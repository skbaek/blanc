import Blanc.Lift.Usdc.LibCreation.Bindings
import Blanc.Lift.BalSilent

/-! Unadopted library-creation preview: effects of the actual retained CREATE.
The original transaction, receipt and history correspondence remain separate. -/

namespace Blanc.Lift.Usdc.LibCreation

open Jaune

/-- The clean retained constructor installs the registered library runtime and
empty storage. Creation preparation supplies the initial empty storage even
when the entry transfers nonzero value. -/
theorem constructor_effects_of_createTrace
    {msg : Msg} {installed : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false)
    (image : msg.code = code) (target : msg.currentTarget = usdcLib)
    (codeAddress : msg.codeAddress = none)
    (stateGas : msg.benv.stat.rules.stateGas = none) :
    installed.getCode msg.currentTarget = Lib.code ∧
      installed.getStor msg.currentTarget = Stor.empty := by
  obtain ⟨benv, raw, charged, transfer, executed, rawClean, charge, source, -⟩ :=
    createTrace_source_witness cert_check image rfl trace clean codeAddress stateGas
  have run : SFunc.Run cert.prog
      (initEvm ((processCreateMessage.msg msg).withBenv benv)).sta
      (St (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna [] Mem.empty
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna.gasLeft)
      t_0000_c0 (.halted raw) := source
  obtain ⟨storage, output⟩ := constructor_effects image target run
  have nonempty : raw.output ≠ [] := by
    rw [output, ByteArray.toList_eq_toList_data]
    decide +kernel
  obtain ⟨result, settled, codeResult, storageResult⟩ :=
    processCreateMessage_effects_of_exec_and_charge msg transfer codeAddress
      executed rawClean charge nonempty
  have same : installed = result := Except.ok.inj (trace.result.symm.trans settled)
  rw [same]
  constructor
  · rw [codeResult]
    apply ByteArray.ext
    rw [← Array.toList_inj]
    change raw.output = Lib.code.data.toList
    rw [← ByteArray.toList_eq_toList_data]
    exact output
  · rw [storageResult, storage]
    exact processCreateMessage_msg_afterTransfer_getStor transfer

/-- The library constructor has no external calls or SELFDESTRUCT; its
retained CREATE preserves the inherited deletion set exactly. -/
theorem constructor_deletions_of_createTrace
    {msg : Msg} {installed : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok installed))
    (clean : installed.error.isSome = false)
    (image : msg.code = code)
    (codeAddress : msg.codeAddress = none)
    (stateGas : msg.benv.stat.rules.stateGas = none) :
    installed.accountsToDelete = msg.inheritedDeletions := by
  obtain ⟨benv, raw, charged, transfer, executed, rawClean, charge, source, installedEq⟩ :=
    createTrace_source_witness cert_check image rfl trace clean codeAddress stateGas
  have frame := SFunc.RunP.balance_deletion_frame_of_balSilent (fun h => h)
    (S := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) source
  have rawDeletion : raw.accountsToDelete = msg.inheritedDeletions :=
    congrArg (fun p => p.2.1) frame
  have chargedDeletion := congrArg Prod.fst (chargeCodeGas_delSets_ok charge)
  rw [installedEq]
  change charged.accountsToDelete = msg.inheritedDeletions
  exact chargedDeletion.trans rawDeletion

end Blanc.Lift.Usdc.LibCreation
