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

/-- Rung R9: a whole retained configured history realizes one PRORATA
accounting replay, from the world at the checkpoint to the world at any
configured continuation of it.

Nothing is added above rung R8's single premise.  The state invariant is
carried from one block to the next by the generic ladder, through the chain
reachability the history itself projects to
(`ConfiguredHistoryTrace.stateInv`), and `prorataSpec.Preserves ca` is
discharged internally from `prorataSpec_preserves` rather than taken as a
hypothesis.  No not-yet-created side condition is threaded at all: each block
re-establishes it from its own empty created-account set, which is what makes
this induction carry exactly one fact.

The blocks are composed in chain order, and each block's steps are tagged with
that block's own header number rather than a synthetic counter. -/
theorem retainedConfiguredHistoryAccountingReplay
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (inv : prorataSpec.StateInv ca checkpoint.state) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca checkpoint.state) steps
        (AccountingSnapshot.ofState ca future.state) := by
  induction history with
  | refl hcfg hctx hid => exact ⟨[], ProrataAccountingReplay.nil_of_eq rfl⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorReplay⟩ := ih
      obtain ⟨blockSteps, blockReplay⟩ :=
        retainedConfiguredBlockAccountingReplay block
          (prior.stateInv (prorataSpec_preserves ca) inv)
          block.block.header.number
      exact ⟨priorSteps ++ blockSteps, priorReplay.append blockReplay⟩

end Prorata

end Blanc
