import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionRewardCredits
import Blanc.ExecutionStagedFrameEnv

/-!
# Block-local facts transported to mid-block (`In`) histories

`MidHistoryTraceIn` (in `ExecutionMidHistoryIn`) starts right after one transaction of a retained
configured block. Its raw roots all lie in the raw roots of retained configured blocks
(`MidHistoryTraceIn.rawFrames_mem_block`), so every per-root block fact transports to it:

* `MidHistoryTraceIn.rewardCreditsFunded` — every block of the mid history, the cut block
  included, funds its own reward credits (`ConfiguredBlockTraceIn.rewardCreditsFunded`);
* `MidHistoryTraceIn.rawFrames_entered` — a guarantee every raw entry of a configured block
  retains (`EnteredCondition`) holds at every raw entry;
* `MidHistoryTraceIn.rootEntryIn` — every raw root starts at pc zero on a selected fork;
* `MidHistoryTraceIn.calldata_bound` — calldata is short on a domain whose nonzero calldata byte
  costs at least 16 gas.

Contract-neutral; no `CoveredFork`.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune

/-- Every block of a mid history funds its reward credits; `stateGas = none` comes per block from
`BodyStageCapabilities F`. -/
theorem MidHistoryTraceIn.rewardCreditsFunded {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) (capabilities : BodyStageCapabilities F) :
    trace.RewardCreditsFunded := by
  induction trace with
  | tail block _ =>
      exact block.rewardCreditsFunded (capabilities.stateGas_none block.forkIn)
  | step _ block ih =>
      exact ⟨ih, block.rewardCreditsFunded (capabilities.stateGas_none block.forkIn)⟩

/-- A guarantee every raw entry of a configured block retains holds at every raw entry of a mid
history. -/
theorem MidHistoryTraceIn.rawFrames_entered {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) (trace : MidHistoryTraceIn F cfg start future) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  intro root member
  obtain ⟨_, _, block, blockMember⟩ := trace.rawFrames_mem_block root member
  exact block.rawFrames_entered hE root blockMember

/-- Every raw root of a mid history starts at pc zero on a selected fork. -/
theorem MidHistoryTraceIn.rootEntryIn {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  intro root member
  obtain ⟨_, _, block, blockMember⟩ := trace.rawFrames_mem_block root member
  exact block.rootEntryIn root blockMember

/-- Every raw root of a mid history has calldata shorter than `2 ^ 256` bytes on a domain whose
nonzero calldata byte costs at least 16 gas. -/
theorem MidHistoryTraceIn.calldata_bound {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F)
    (hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  intro root member
  obtain ⟨_, _, block, blockMember⟩ := trace.rawFrames_mem_block root member
  exact block.calldata_bound capabilities hdata root blockMember

end ExecutionTrace

end Blanc
