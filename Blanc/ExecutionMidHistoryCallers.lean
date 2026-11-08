import Blanc.ExecutionInCodeImage
import Blanc.ExecutionMidHistoryIn
import Blanc.Lift.CallChildren
import Blanc.ExecutionTraceRootCallers
import Blanc.ExecutionMidHistoryInCallerExclusion
import Blanc.ExecutionHistoryCommittedCuts
import Blanc.ExecutionSenderRootCallers

/-!
# Retained caller provenance for selected-domain whole and mid-block histories

These are settlement-forest facts. They impose no fork capability, code image,
storage invariant or successful-outcome assumption beyond the retained trace.
The caller's root and direct-child obligations remain explicit.
-/

namespace Blanc.ExecutionTrace

open Jaune



/-- The caller fold over a selected fork-domain history. -/
theorem ConfiguredHistoryTraceIn.settledFrames_callerTarget_of_children
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {p ca : Adr} {Q : Sevm → Prop} (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (roots : ∀ R ∈ trace.settledRoots, CallerTarget p ca Q R.sevm)
    (children : ∀ G ∈ trace.settledFrames, CallerChildren p ca Q G.sevm (Exec.childFrames G.run)) :
    ∀ G ∈ trace.settledFrames, CallerTarget p ca Q G.sevm := by
  rw [trace.settledFrames_eq] at children ⊢
  exact rootFrames_callerTarget_of_children trace.settledRoots roots children

/-- The same caller fold starts at the actual transaction cut, without including
the deployment transaction or earlier transactions in its retained forest. -/
theorem MidHistoryTraceIn.settledFrames_callerTarget_of_children
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    {p ca : Adr} {Q : Sevm → Prop} (trace : MidHistoryTraceIn F cfg start future)
    (roots : ∀ R ∈ trace.settledRoots, CallerTarget p ca Q R.sevm)
    (children : ∀ G ∈ trace.settledFrames, CallerChildren p ca Q G.sevm (Exec.childFrames G.run)) :
    ∀ G ∈ trace.settledFrames, CallerTarget p ca Q G.sevm := by
  rw [trace.settledFrames_eq] at children ⊢
  exact rootFrames_callerTarget_of_children trace.settledRoots roots children




end Blanc.ExecutionTrace
