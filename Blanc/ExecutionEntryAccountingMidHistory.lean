import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.ExecutionMidHistoryInFacts

/-!
# The carried invariant at committed target frames of a mid-block history

`ConfiguredHistoryTrace.entryGood_settled` (`ExecutionEntryAccounting.lean`) replays a
whole-block history from a checkpoint. A history rooted at an actual transaction (a
deployment, say) starts right after that transaction instead: a `MidHistoryTraceIn` on the
covered fork domain. This module states the same conclusion for it, through the covered
instance of the entry ladder (`AccountingLadderAdmitted.toIn`) and the mid-history replay
rung (`AccountingLadderAdmittedIn.midHistoryIn`). The mid-history rung additionally consumes
the installed certificate of the contract's code; reward funding is derived from the fork
domain. Contract-neutral.
-/

namespace Blanc

open Jaune ExecutionAccountingReplay

namespace ExecutionTrace

/-- **The carried invariant at the entry of every committed target frame of a mid-block
history.** As `ConfiguredHistoryTrace.entryGood_settled`, for a covered-fork history starting
right after one transaction of a retained block. -/
theorem MidHistoryTraceIn.entryGood_settled {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop} {I : Stor → Prop}
    {cfg : ChainConfig} {start : Benv} {future : BlockChain} {C : ByteArray}
    (trace : MidHistoryTraceIn CoveredFork cfg start future)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca start.state) (initial : I (start.state.getStor ca))
    (preserves : c.PreservesAdmitted ca entry)
    (preserve : FramePreserves ca c.sem entry I) (kinds : SpawnKinds ca c.sem)
    (spawn : SpawnEntry ca c.sem entry I)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    I (future.state.getStor ca) ∧
      ∀ f ∈ trace.settledFrames, f.sevm.currentTarget = ca → f.sevm.isStatic = false →
        EntryGood ca c.sem entry I f := by
  obtain ⟨steps, replay, observed⟩ :=
    (entryLadder preserves preserve kinds spawn).toIn.midHistoryIn trace admitted
      BodyStageCapabilities.covered (trace.rewardCreditsFunded BodyStageCapabilities.covered)
      inv K image
  obtain ⟨final, good⟩ := replay initial
  change steps = trace.settledFrames.flatMap (fun f : Exec.Frame =>
    if f.sevm.currentTarget = ca ∧ f.sevm.isStatic = false then [f] else []) at observed
  refine ⟨final, fun f member target static => good f ?_⟩
  rw [observed]
  exact List.mem_flatMap.mpr ⟨f, member, by simp only [target, static, and_self, ↓reduceIte,
    List.mem_cons, List.not_mem_nil, or_false]⟩

end ExecutionTrace

end Blanc
