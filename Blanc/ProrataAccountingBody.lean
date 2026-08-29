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

end Prorata

end Blanc
