import Blanc.DeploymentMessage
import Blanc.MessageExecution

/-!
# Successful deployment settlement with recorded touches

These forward bridges keep the rules-selected touch in the exact settled
machine. Constructor execution and code-deposit affordability remain actual
local witnesses; no fork-domain or endpoint-state premise is introduced.
-/

namespace Blanc

open Jaune

/-- A clean total execution settles with its actual target touch retained. -/
theorem processMessage_ok_touch_of_exec
    {msg : Msg} {benv : Benv} {raw : Devm}
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hcodeAddress : msg.codeAddress = none)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok raw)
    (herror : raw.error = none) :
    processMessage msg =
      .ok (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) := by
  rw [MessageExecution.processMessage_eq_settle_exec_afterTransfer_of_noCodeAddress
    msg benv htransfer hcodeAddress, hexec]
  simp only [Frame.settle, Frame.settleMsg, Frame.ofCall, executeCode.handleErrorWith_ok,
    Bool.false_eq_true, ↓reduceIte, processMessage.settle, Except.bind_ok,
    herror, Option.isSome_none]

/-- A clean constructor's touched result, followed by actual successful code
charging, settles with the charged output installed at its created target. -/
theorem processCreateMessage_ok_touch_of_exec_and_charge
    (msg : Msg) {benv : Benv} {raw charged : Devm}
    (htransfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (hcodeAddress : msg.codeAddress = none)
    (hexec : exec (initEvm ((processCreateMessage.msg msg).withBenv benv)) = .ok raw)
    (herror : raw.error = none)
    (hcharge : processCreateMessage.chargeCodeGas msg.benv.stat.rules
      (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) = .ok charged) :
    processCreateMessage msg =
      .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩) := by
  refine processCreateMessage_ok_of_processMessage_and_charge msg
    (processMessage_ok_touch_of_exec htransfer hcodeAddress hexec herror) ?_ hcharge
  exact (Devm.recordTouch_error raw msg.benv.stat.rules true msg.currentTarget).trans herror

/-- Actual touch and code charging preserve storage; installing nonempty
output retains that storage even under account normalization. -/
theorem createCharge_install_effects
    {rules : ForkRules} {target : Adr} {raw charged : Devm}
    (charge : processCreateMessage.chargeCodeGas rules
      (raw.recordTouch rules true target) = .ok charged)
    (nonempty : raw.output ≠ []) :
    (charged.setCode target ⟨⟨charged.output⟩⟩).getCode target = ⟨⟨raw.output⟩⟩ ∧
      (charged.setCode target ⟨⟨charged.output⟩⟩).getStor = raw.getStor := by
  have state : charged.state = raw.state :=
    (chargeCodeGas_state_ok charge).trans (Devm.recordTouch_state _ _ _ _)
  have output : charged.output = raw.output := by
    rw [processCreateMessage.chargeCodeGas_ok_eq_setMach charge]
    exact Devm.recordTouch_output _ _ _ _
  have notEmpty : ¬ ({charged.state.get target with code :=
      ⟨⟨charged.output⟩⟩} : Acct).Empty := by
    intro empty
    have length : charged.output.length = 0 := empty.1
    exact nonempty (List.eq_nil_of_length_eq_zero (output ▸ length))
  constructor
  · change (charged.state.setCode target _).getCode target = _
    simp only [State.setCode, State.getCode, State.setAccount_get_self,
      Acct.clearIfEmpty_code, output]
  · rw [Devm.setCode_getStor]
    funext a
    split
    · next h => exact (notEmpty h.2).elim
    · change charged.state.getStor a = raw.state.getStor a
      rw [state]

/-- Project a clean constructor's actual CREATE settlement without assuming
the installed code or storage. Nonempty output rules out account erasure. -/
theorem processCreateMessage_effects_of_exec_and_charge
    (msg : Msg) {benv : Benv} {raw charged : Devm}
    (transfer : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv)
    (codeAddress : msg.codeAddress = none)
    (executed : exec (initEvm ((processCreateMessage.msg msg).withBenv benv)) = .ok raw)
    (clean : raw.error = none)
    (charge : processCreateMessage.chargeCodeGas msg.benv.stat.rules
      (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) = .ok charged)
    (nonempty : raw.output ≠ []) :
    ∃ installed, processCreateMessage msg = .ok installed ∧
      installed.getCode msg.currentTarget = ⟨⟨raw.output⟩⟩ ∧
      installed.getStor = raw.getStor := by
  exact ⟨_, processCreateMessage_ok_touch_of_exec_and_charge msg transfer codeAddress
    executed clean charge, createCharge_install_effects charge nonempty⟩

end Blanc
