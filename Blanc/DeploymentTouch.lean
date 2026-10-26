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

end Blanc
