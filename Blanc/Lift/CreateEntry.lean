import Blanc.TransactionForward
import Blanc.Lift.Deploy

/-! # The exact entry world of a zero-value CREATE frame

`processCreateMessage` clears the target's storage, increments its nonce, and moves the message
value (here zero) from the caller to the target. `entryState` is that world as an explicit term
of the input world: the same `State` operations in the same order, so a later closed evaluation
over a concrete input world (for example a message's `origState`) can reduce it. This complements
the account-by-account form `processCreateMessage_msg_afterTransfer_get`. -/

namespace Blanc.Lift.CreateEntry

open Jaune

/-- The world a zero-value, value-transferring CREATE frame enters with: target storage cleared
and nonce incremented, then the zero debit of `caller` and the zero credit of `tgt`. -/
def entryState (W : State) (caller tgt : Adr) : State :=
  let S := (W.setStor tgt .empty).incrNonce tgt
  (S.setBal caller (S.bal caller - 0)).addBal tgt 0

/-- **The entry world, exactly.** -/
theorem entry_state {msg : Msg} {benv : Benv} (hzero : msg.value = 0)
    (hstv : msg.shouldTransferValue = true)
    (h : (processCreateMessage.msg msg).benvAfterTransfer = .ok benv) :
    benv.state = entryState msg.benv.state msg.caller msg.currentTarget := by
  obtain ⟨mid, hsub, rfl⟩ := of_benvAfterTransfer (msg := processCreateMessage.msg msg) hstv h
  obtain ⟨-, rfl⟩ := State.of_subBal hsub
  change ((_ : State).setBal _ _).addBal _ _ = _
  rw [show (processCreateMessage.msg msg).value = 0 from hzero]
  rfl

/-- The settled world of a lifted CREATE as a term: the constructor's world with the returned
code installed at the target. -/
theorem liftCreatePost_state (target : Adr) (raw : Devm) :
    (liftCreatePost target raw).state = raw.state.setCode target ⟨⟨raw.output⟩⟩ := rfl

end Blanc.Lift.CreateEntry
