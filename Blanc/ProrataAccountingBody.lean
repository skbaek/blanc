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
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca benv.state) steps
        (AccountingSnapshot.ofState ca finalBenv.state) := by
  induction trace with
  | nil => exact ⟨[], ProrataAccountingReplay.nil_of_eq rfl⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail
      ih =>
      obtain ⟨headSteps, headReplay⟩ :=
        retainedTransactionAccountingReplay head inv notCreated blockIndex
          (some index)
      have next : prorataSpec.BenvInv ca (benv.withState txState) :=
        head.benvInv (prorataSpec_preserves ca) inv.side ⟨inv, notCreated⟩
      obtain ⟨tailSteps, tailReplay⟩ := ih next.state next.ca
      exact ⟨headSteps ++ tailSteps, headReplay.append tailReplay⟩

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
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca benv.state) steps
        (AccountingSnapshot.ofState ca state) := by
  have msgInv : prorataSpec.MsgInv ca
      (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv inv notCreated
  have ready : AccountingMessageReady ca
      (systemTransactionMessage benv target data) := by
    refine ⟨msgInv.runReady_of_call
      (systemTransactionMessage_target_isNone benv target data), ?_⟩
    intro current
    rw [systemTransactionMessage_currentTarget] at current
    rw [systemTransactionMessage_caller]
    exact fun collide => systemNe (current.trans collide.symm)
  have replay :=
    retainedMessageCallAccountingReplay trace.message ready blockIndex none
  rwa [systemTransactionMessage_benv_state] at replay

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
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca benv.state) steps
        (AccountingSnapshot.ofState ca state) := by
  obtain ⟨withdrawalSteps, withdrawalReplay⟩ :=
    retainedSystemMessageAccountingReplay trace.withdrawal inv notCreated
      (by decide) blockIndex
  have withdrawalInv : prorataSpec.BenvInv ca
      (benv.withState trace.withdrawalState) :=
    trace.withdrawal.benvInv (prorataSpec_preserves ca) ⟨inv, notCreated⟩
  obtain ⟨consolidationSteps, consolidationReplay⟩ :=
    retainedSystemMessageAccountingReplay trace.consolidation
      withdrawalInv.state withdrawalInv.ca (by decide) blockIndex
  refine ⟨withdrawalSteps ++ consolidationSteps, ?_⟩
  rw [RequestsTrace.state_eq_consolidationState trace]
  exact withdrawalReplay.append consolidationReplay

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
        (AccountingSnapshot.ofState ca pre) steps
        (AccountingSnapshot.ofState ca (processWithdrawalsState pre wds)) := by
  induction wds generalizing pre with
  | nil => exact ⟨[], ProrataAccountingReplay.nil_of_eq rfl⟩
  | cons wd wds ih =>
      obtain ⟨headBound, tailBound⟩ := withdrawalCredit_bounds bound
      let provenance : ProrataAccountingProvenance :=
        { blockIndex := blockIndex
          transactionIndex := none
          framePath := []
          actor := none }
      obtain ⟨headSteps, headReplay⟩ :=
        ProrataAccountingReplay.of_addBal (ca := ca) (target := wd.recipient)
          provenance headBound
      obtain ⟨tailSteps, tailReplay⟩ := ih _ tailBound
      refine ⟨headSteps ++ tailSteps, ?_⟩
      rw [processWithdrawalsState_cons]
      exact headReplay.append tailReplay

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
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca benv.state) steps
        (AccountingSnapshot.ofState ca state) := by
  -- (1) The beacon-roots system message.
  obtain ⟨beaconSteps, beaconReplay⟩ :=
    retainedSystemMessageAccountingReplay trace.beacon inv notCreated
      (by decide) blockIndex
  have beaconMeta :=
    trace.beacon.stateInv_and_sum_le (c := prorataSpec)
      (prorataSpec_preserves ca) ⟨inv, notCreated⟩
  have beaconInv : prorataSpec.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beaconMeta.1, by simpa [Benv.withState] using notCreated⟩
  -- (2) The history-storage system message.
  obtain ⟨historySteps, historyReplay⟩ :=
    retainedSystemMessageAccountingReplay trace.history beaconInv.state
      beaconInv.ca (by decide) blockIndex
  have historyMeta :=
    trace.history.stateInv_and_sum_le (prorataSpec_preserves ca) beaconInv
  have historyInv : prorataSpec.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨historyMeta.1, by simpa [Benv.withState] using beaconInv.ca⟩
  -- (3) The decoded transaction list, by rung R3.
  obtain ⟨txSteps, txReplay⟩ :=
    retainedTransactionListAccountingReplay trace.transactions
      historyInv.state historyInv.ca blockIndex
  have txInv : prorataSpec.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv (prorataSpec_preserves ca) historyMeta.1.side
      historyInv
  -- (4) The direct consensus withdrawals, by rung R6.  Their bound is the
  -- block bound transported through the balance-nonincreasing prefix.
  have txBound :
      sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    have hbeacon := beaconMeta.2
    have hhistory : sum trace.historyState.bal ≤ sum trace.beaconState.bal := by
      simpa [Benv.withState] using historyMeta.2
    have htx : sum trace.transactionBenv.state.bal ≤
        sum trace.historyState.bal := by
      simpa [Benv.withState] using trace.transactions.sum_le
    omega
  obtain ⟨wdSteps, wdReplay⟩ :=
    retainedDirectWithdrawalAccountingReplay (ca := ca)
      trace.transactionBenv.state wds txBound blockIndex
  have wdInv := benvInv_processWithdrawalsState txInv txBound
  -- (5) The two request system calls, by rung R5.
  obtain ⟨requestSteps, requestReplay⟩ :=
    retainedRequestsAccountingReplay trace.requests wdInv.state wdInv.ca
      blockIndex
  exact ⟨beaconSteps ++ (historySteps ++ (txSteps ++ (wdSteps ++ requestSteps))),
    beaconReplay.append (historyReplay.append
      (txReplay.append (wdReplay.append requestReplay)))⟩

end Prorata

end Blanc
