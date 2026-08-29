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

end Prorata

end Blanc
