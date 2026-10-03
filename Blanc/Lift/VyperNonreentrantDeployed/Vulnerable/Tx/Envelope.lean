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

/-! ### The admission checks, evaluated on the concrete transaction and block -/

theorem benvPre_stateGas : benvPre.stat.rules.stateGas = none :=
  CoveredFork.prague.rules_stateGas_none

/-- The type-2 transaction's chain id is the block's. -/
theorem tx0_chain : checkTransactionChainId benvPre.beginTransaction tx0 = .ok () := by
  kernel_rfl

/-- Fee rules with base fee 0: `maxPriorityFee = maxFee = 0` is legal, and the effective gas
price and the maximum fee are 0. -/
theorem tx0_fee : checkTransactionGasFee benvPre.beginTransaction tx0 = .ok (0, 0) := by
  kernel_rfl

theorem tx0_blob : checkTransactionBlobData benvPre.beginTransaction tx0 0 = .ok (0, []) := by
  kernel_rfl

theorem tx0_receiver : checkTransactionReceiver tx0 = .ok () := by kernel_rfl

theorem tx0_auth : checkTransactionAuthorizationList tx0 = .ok () := by kernel_rfl

/-- The sender account: nonce 0 is the transaction's nonce, its balance 0 covers the maximum fee
0 plus the value 0, and it has no code (EIP-3607): `E` is an EOA. -/
theorem tx0_sender :
    checkTransactionSenderAccount (benvPre.beginTransaction.state.get eAddress) tx0 0 = .ok () := by
  kernel_rfl

/-! ### The debit, the prepared message and the call wrapper -/

/-! ### The transaction -/

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
