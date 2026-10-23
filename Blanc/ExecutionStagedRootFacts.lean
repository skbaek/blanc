import Blanc.ExecutionStagedFrameEnv
import Blanc.ExecutionStagedAdmission

/-!
# Machine entry facts at the raw frames of a selected-domain history

Every raw frame root retained by a `ConfiguredHistoryTraceIn` starts at
program counter zero on a selected fork, with no state gas, an empty stack
and memory, and less than one word of gas. The facts come from the history
itself (`rootEntryIn`, `rawFrame_gas`, `rawFrames_entered`) and the selected
domain's `BodyStageCapabilities`; no per-frame premise is added. These are the
root-form inputs of `lift_sound_in_noStateGas` and of potential-carrying
frame walks.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- **Entry facts at every raw frame of a selected-domain history**: pc zero,
selected fork, no state gas, fresh stack and memory, and word-bounded gas. -/
theorem ConfiguredHistoryTraceIn.rawFrame_entryFacts {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) :
    ∀ R ∈ history.rawFrames, R.pc = 0 ∧ F R.sevm.benvStat.fork ∧
      R.sevm.benvStat.rules.stateGas = none ∧ Exec.FreshEntry R.sevm R.devm ∧
      R.devm.gasMeasure < 2 ^ 256 := by
  intro R member
  obtain ⟨pc, fork⟩ := history.rootEntryIn R member
  exact ⟨pc, fork, capabilities.stateGas_none fork,
    history.rawFrames_entered enteredCondition_fresh R member,
    history.rawFrame_gas capabilities R member⟩

end ExecutionTrace

end Blanc
