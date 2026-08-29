-- ProrataAccountingHistory.lean : configured block and chain accounting replay.

import Blanc.ProrataAccountingBody
import Blanc.ExecutionHistoryEffects

namespace Blanc

open Jaune

namespace Prorata

open _root_.Blanc.ExecutionTrace

/-- Rung R8: a whole configured block realizes one PRORATA accounting replay,
from the world the parent chain leaves to the world the imported block
installs.

Nothing is added above rung R7's premises -- and one is removed.  The block
carrier owns its own `wdsum` bound as a structure field, so R7's added
hypothesis is discharged here and reaches no rung above this one.  The
not-yet-created side condition disappears entirely: block preparation opens
`applyBody` on an empty created-account set
(`ConfiguredBlockTrace.not_mem_openingCreatedAccounts`), so R8 asks only for
the state invariant at the parent chain.

The block-preparation boundary contributes no accounting step, because it
moves no value: `initBenv` copies the parent chain's world state verbatim. -/
theorem retainedConfiguredBlockAccountingReplay
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (inv : prorataSpec.StateInv ca pre.state)
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca pre.state) steps
        (AccountingSnapshot.ofState ca post.state) := by
  obtain ⟨steps, replay⟩ :=
    retainedBodyAccountingReplay (ca := ca) trace.bodyTrace
      (trace.openingState ▸ inv)
      (trace.not_mem_openingCreatedAccounts ca)
      trace.openingBound blockIndex
  refine ⟨steps, ?_⟩
  rw [trace.postState]
  rwa [trace.openingState] at replay

end Prorata

end Blanc
