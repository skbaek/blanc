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

/-- Every raw frame of a retained `In`-history is a system or a transaction frame. -/
theorem ConfiguredHistoryTraceIn.rawFrames_system_or_tx
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    ∀ root ∈ trace.rawFrames, root ∈ trace.systemRawFrames ∨ root ∈ trace.txRawFrames := by
  induction trace with
  | refl => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTraceIn.rawFrames, ConfiguredHistoryTraceIn.systemRawFrames,
        ConfiguredHistoryTraceIn.txRawFrames, List.mem_append] at member ⊢
      rcases member with member | member
      · rcases ih root member with h | h
        · exact .inl (.inl h)
        · exact .inr (.inl h)
      · simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames,
          ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames,
          List.mem_append] at member ⊢
        rcases member with ((h | h) | h) | h
        · exact .inl (.inr (.inl (.inl h)))
        · exact .inl (.inr (.inl (.inr h)))
        · exact .inr (.inr h)
        · exact .inl (.inr (.inr h))

/-- Children keep the code at an address no CREATE frame of the history targets. -/
theorem ConfiguredHistoryTraceIn.childFrames_codeAt_keep
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {a : Adr}
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    ∀ root ∈ trace.rawFrames, ∀ c ∈ Exec.childFrames root.exc,
      c.post.getCode a = c.pre.getCode a := by
  intro root member
  exact Exec.childFrames_codeAt_keepH root.exc
    (capabilities.stateGas_none (trace.rootEntryIn root member).2)
    (fun d hd => noFrame d (trace.rawFrames_closed root member d hd))

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
