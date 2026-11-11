import Blanc.ExecutionOccurrence
import Blanc.ExecutionTrace
import Init.Data.Ord.UInt
import Blanc.DeploymentMessage

namespace Blanc

open Jaune

/-- A successful raw `exec` with no frame error settles as the corresponding
ordinary message result. -/
theorem processMessage_ok_of_exec
    {msg : Msg} {benv : Benv} {post : Devm}
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hcodeAddress : msg.codeAddress = .none)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = .none)
    (hsweep : msg.benv.stat.rules.settle.touchedSweep = false) :
    processMessage msg = .ok post := by
  unfold processMessage runFrame Frame.enter Frame.ofCall
  rw [htransfer]
  unfold executeCode.enter
  simp only [Msg.withBenv, hcodeAddress]
  unfold Frame.settle Frame.settleMsg
  simp only [Msg.withBenv, hcodeAddress] at hexec
  rw [hexec]
  simp only [Bool.false_eq_true, ↓reduceIte, processMessage.settle, executeCode.handleErrorWith_ok,
    Except.bind_ok, herror, Option.isSome_none, Devm.recordTouch_of_not_touchedSweep hsweep]

/-- The outer message result induced by a successful direct CREATE after code
charging.  Constructor families may retain their historical wrapper names,
but the projection itself is contract-neutral. -/
def directCreateMessageOutputOf (post : Devm) : MsgCallOutput :=
  { gasLeft := post.gasLeft
    refundCounter := 0
    logs := post.logs
    accountsToDelete := post.accountsToDelete
    error := post.error
    returnData := post.output
    touchedAccounts := post.meta.touchedAccounts }

/-! ## Contract-neutral protocol-deployment plumbing -/

end Blanc
