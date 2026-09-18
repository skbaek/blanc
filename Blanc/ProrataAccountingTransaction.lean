-- ProrataAccountingTransaction.lean : transaction-level accounting replay.

import Blanc.ProrataAccountingExec
import Blanc.ExecutionTransactionEffects

namespace Blanc

open Jaune

namespace Prorata

open _root_.Blanc.ExecutionTrace

/-- The transaction's prepared message is accounting-ready unless it is a
CREATE aimed at PRORATA's own address, and that case cannot run any code: an
installed contract's compiled bytes make the create-collision test fire, so
the wrapper leaves the world exactly as it found it. -/
theorem TransactionTrace.messageAccountingReplay
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (msgInv : prorataSpec.MsgInv ca trace.msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca trace.msg.benv.state) steps
        (RealizedSnapshot.ofState ca trace.messageState) :=
  (accountingLadder ca).transactionMessage trace msgInv msgInv.state.side
    blockIndex transactionIndex

/-- Rung R2: one whole successful transaction realizes a complete PRORATA
accounting replay, from the world it opens on to its exact final state.

The transaction moves PRORATA's world in five places and each is discharged
without a new side condition.  The nonce bump and up-front gas debit cannot
touch PRORATA because a checked sender is never an installed contract; the
prepared message reuses rung R1; the sender gas refund misses PRORATA for the
same sender reason; the coinbase priority fee is the one place this rung
*adds* a step, and `ProrataAccountingReplay.of_addBal` supplies SF §5's
positive/zero split for a coinbase that may or may not be PRORATA itself; and
the final account-deletion fold never names an installed contract.  Both
credits are funded out of the transaction's own up-front debit, so neither
needs a wrap-around hypothesis. -/
theorem retainedTransactionAccountingReplay
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : prorataSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca benv.state) steps
        (RealizedSnapshot.ofState ca state) :=
  (accountingLadder ca).transaction trace inv notCreated inv.side blockIndex
    transactionIndex

end Prorata

end Blanc
