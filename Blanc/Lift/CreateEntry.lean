import Blanc.TransactionForward
import Blanc.Lift.Deploy

/-! # The exact entry world of a zero-value CREATE frame

`processCreateMessage` clears the target's storage and increments its nonce. A zero message
value leaves the resulting world unchanged by transfer; no debit or credit is performed. `entryState` is that world as an explicit term
of the input world: the same `State` operations in the same order, so a later closed evaluation
over a concrete input world (for example a message's `origState`) can reduce it. This complements
the account-by-account form `processCreateMessage_msg_afterTransfer_get`. -/

namespace Blanc.Lift.CreateEntry

open Jaune

/-- The world a zero-value, value-transferring CREATE frame enters with: target storage cleared
and nonce incremented. The retained caller parameter does not affect zero-value entry. -/
def entryState (W : State) (caller tgt : Adr) : State :=
  (W.setStor tgt .empty).incrNonce tgt

/-- **The entry world, exactly.** -/
theorem entry_state {msg : Msg} {benv : Benv} (hzero : msg.value = 0)
    (hstv : msg.shouldTransferValue = true)
    (h : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv) :
    benv.state = entryState msg.benv.state msg.caller msg.currentTarget := by
  rw [Msg.benvAfterTransfer_of_value_zero (show (processCreateMessage.msg msg).value = 0 from hzero)] at h
  cases h
  rfl

/-- The settled world of a lifted CREATE as a term: the constructor's world with the returned
code installed at the target. -/
theorem liftCreatePost_state (target : Adr) (raw : Devm) :
    (liftCreatePost target raw).state = raw.state.setCode target ⟨⟨raw.output⟩⟩ := rfl

end Blanc.Lift.CreateEntry
