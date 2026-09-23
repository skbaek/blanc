-- ProrataAccountingBody.lean : block-body accounting replay.

import Blanc.ProrataAccountingTransaction
import Blanc.ExecutionBodyEffects

namespace Blanc

open Jaune

namespace Prorata

open _root_.Blanc.ExecutionTrace

/-- Rung R3: a whole retained transaction list realizes one PRORATA
accounting replay, from the world it opens on to the world it leaves.

Nothing is added above rung R2's own premises.  `TransactionTrace.benvInv`
carries the state invariant and the not-yet-created side condition from one
transaction to the next, and `prorataSpec.Preserves ca` is discharged
internally from `prorataSpec_preserves` rather than taken as a hypothesis. -/
theorem retainedTransactionListAccountingReplay
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : prorataSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca benv.state) steps
        (RealizedSnapshot.ofState ca finalBenv.state) :=
  (accountingLadder ca).transactionList trace inv notCreated inv.side hfork blockIndex

/-- Rung R4: a retained Jaune system message realizes one PRORATA accounting
replay.

No disjointness between PRORATA's address and the four predeploy addresses is
needed, and none is available: predeploys are ordinary code accounts.  The
`currentTarget = ca` branch is discharged from the state invariant's own code
field, exactly as the message rung already does for an ordinary call.

The one side condition is about the system target alone, never about `ca`:
a system message is sent by the fixed `systemAddress`, so ruling out a
self-withdrawal root at a system target equal to `ca` needs only that the
target is not itself the system address.  Every one of the four call sites
below discharges it by `decide` on concrete addresses, so no rung above this
one carries it. -/
theorem retainedSystemMessageAccountingReplay
    {ca : Adr} {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (inv : prorataSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca benv.state) steps
        (RealizedSnapshot.ofState ca state) :=
  (accountingLadder ca).systemMessage trace inv notCreated systemNe inv.side hfork
    blockIndex

/-- Rung R5: the two checked request-system calls at the tail of `applyBody`
realize one PRORATA accounting replay.  Both are rung R4, composed at the
world the first one leaves; each system target's disequality from
`systemAddress` is settled on concrete addresses. -/
theorem retainedRequestsAccountingReplay
    {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (inv : prorataSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca benv.state) steps
        (RealizedSnapshot.ofState ca state) :=
  (accountingLadder ca).requests trace inv notCreated inv.side hfork blockIndex

/-- Rung R6: the block's direct consensus withdrawals realize one PRORATA
accounting replay -- one `externalCredit` step per *positive* credit to
PRORATA, and no step at all for a zero credit or a credit to anyone else.
`ProrataAccountingReplay.of_addBal` performs exactly that split, as it already
does for rung R2's coinbase priority fee.

The block bound is what makes each credit exact.  Without it a withdrawal
could wrap PRORATA's balance, and a wrapped credit is not an external-credit
step; the same bound is what the generic `applyBody` invariant rung asks
for. -/
theorem retainedDirectWithdrawalAccountingReplay
    {ca : Adr} (pre : State) (wds : List Withdrawal)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256)
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca pre) steps
        (RealizedSnapshot.ofState ca (processWithdrawalsState pre wds)) :=
  (accountingLadder ca).directWithdrawal pre wds bound blockIndex

/-- Rung R7: a whole successful block body realizes one PRORATA accounting
replay, from the world the body opens on to the exact world `applyBody`
leaves.

The five segments are composed in `applyBody`'s own order -- beacon-roots
system message, history-storage system message, decoded transaction list,
direct consensus withdrawals, request system calls -- which is the order
`AppliedBodyStateChronology.stateBoundaries` lays the matching state
boundaries out in.

Above the transaction rung's own premises this asks only for the block's
`wdsum` bound, which rung R6 needs to make each withdrawal credit exact and
which the generic `applyBody` invariant rung asks for in the same words.  No
disjointness between PRORATA's address and the four predeploy addresses is
required anywhere. -/
theorem retainedBodyAccountingReplay
    {ca : Adr} {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (inv : prorataSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork)
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (RealizedSnapshot.ofState ca benv.state) steps
        (RealizedSnapshot.ofState ca state) :=
  (accountingLadder ca).body trace inv notCreated bound hfork blockIndex

end Prorata

end Blanc
