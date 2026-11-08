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

end Blanc.Lift.CreateEntry
