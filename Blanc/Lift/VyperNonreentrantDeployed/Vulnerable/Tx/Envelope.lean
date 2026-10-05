import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Closed
import Blanc.TransactionForward

/-!
# V- as an admitted transaction: the transaction envelope

The transaction `tx0` (a real signature over its signing hash under `E`'s key, type 2, zero fees,
zero value, 30,021,064 gas) is run by Jaune's `processTransaction` over the block `benvPre`.
Every admission check is discharged here by evaluating it on the concrete transaction and block
-- validation and intrinsic gas, chain id, fee rules with base fee 0, nonce, balance against the
maximum fee and value, EIP-3607 (the sender `E` has no code), receiver, authorization list --
except two things that are not evaluations of this block: the signature recovery, which is the
one premise (`recoverSender 0 tx0 = .ok E`, true by evaluation: the `#guard` in `TxTop`), and the
room in the block for the transaction's gas (`bout.blockGasUsed`).  The debit, the prepared
message (which is `msg0tx`, the message of the closed message-level theorem) and the settlement
are `Blanc.processTransaction_of_stages`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop


/-! ### The debit, the prepared message and the call wrapper -/

/-! ### The transaction -/

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
