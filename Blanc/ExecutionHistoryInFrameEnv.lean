import Blanc.ExecutionTraceFrameEnv
import Blanc.ExecutionHistoryInWarmth
import Blanc.ExecutionHistoryInCodeAt
import Blanc.ExecutionHistoryInSystemFrames
import Blanc.ExecutionStagedSstoreAttribution
import Blanc.ExecutionStagedFrameEnv
import Blanc.ExecutionMidHistoryInForest
import Blanc.ExecutionMidHistoryInFacts

/-!
# Frame-environment facts along selected-domain histories

`In` forms of the facts `Blanc/ExecutionTraceFrameEnv.lean` proves over covered forks: raw frames are
system or transaction frames, children keep the code at an address no CREATE frame targets, and a
precompile is warm and undelegated at every transaction frame. Nothing here mentions a contract.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}

/-- **A precompile is warm and undelegated at every transaction frame of a historical history.** -/
theorem ConfiguredHistoryTraceIn.precompileReadyH {a : Adr}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (capabilities : BodyStageCapabilities HistFork)
    (precompile : ∀ f, HistFork f → a ∈ (Fork.ruleSet f).precompiles)
    (checkpointEmpty : checkpoint.state.getCode a = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt a)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.txRawFrames, getDelegatedCodeAddress (root.devm.getCode a) = none ∧
      a ∈ root.devm.accessedAddresses := by
  intro root member
  obtain ⟨hcode, -⟩ := trace.codeAt_empty_noStateGas capabilities
    (fun _ hf hp => hf.delegationDisabled_of_prePrague hp) noAuthority noFrame checkpointEmpty
  refine ⟨?_, trace.txRawFrames_warmIn capabilities precompile root member⟩
  have hnot : ¬ isValidDelegation ByteArray.empty := fun h => absurd h.1 (by decide)
  rw [hcode root member]
  simp only [getDelegatedCodeAddress, hnot, ↓reduceIte]

end ExecutionTrace

end Blanc
