import Blanc.ExecutionMidHistoryInCallerExclusion
import Blanc.ExecutionHistoryInEraBounds

/-!
# Caller exclusion before Cancun, starting at an original transaction cut

The accepted final tip bounds all earlier selected forks. Disabled system
stages contribute no frames, and disabled delegation needs no authority
exclusion. Initial empty code, checked-sender exclusion and entered-creation
avoidance remain separate hypotheses; no endpoint absence is inferred.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- A pre-Cancun mainnet block has only transaction frames. Its actual fork
supplies the capabilities for empty-code transport and caller exclusion. -/
theorem ConfiguredBlockTraceIn.callers_and_code_empty_before_cancun
    {pre post : BlockChain} {a : Adr}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (early : block.block.header.timestamp < mainnetCancunTimestamp)
    (senders : block.bodyTrace.transactions.NoSenderAt a)
    (avoid : ∀ root ∈ block.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (empty : pre.state.getCode a = ByteArray.empty) :
    (∀ root ∈ block.rawFrames, root.sevm.caller ≠ a) ∧
      post.state.getCode a = ByteArray.empty := by
  have era := mainnetChainConfig_preCancun_of_timestamp_lt block.forkAt early
  have disabled := block.systemStagesDisabled_of_mainnet_timestamp_lt early
  have frames : block.rawFrames = block.bodyTrace.transactions.rawFrames := by
    simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames,
      block.bodyTrace.beacon.rawFrames_of_disabled disabled.1,
      block.bodyTrace.history.rawFrames_of_disabled disabled.2.1,
      block.bodyTrace.requests.rawFrames_of_disabled disabled.2.2,
      List.nil_append, List.append_nil]
  obtain ⟨roots, final⟩ := block.codeAt_empty_noStateGas BodyStageCapabilities.historical
    (Or.inl (block.forkIn.delegationDisabled_of_prePrague era.toPrePrague)) avoid empty
  refine ⟨?_, final⟩
  rw [frames]
  exact block.bodyTrace.transactions.caller_excluded_noStateGas
    (HistFork.stateGas_none block.forkIn) senders roots (by simpa only [frames] using avoid)

/-- Original mid-history caller exclusion follows from a final accepted tip
before Cancun. This derives the era of every retained block rather than asking
for a per-block fork or protocol-frame oracle. -/
theorem MidHistoryTraceIn.callers_and_code_empty_before_cancun
    {start : Benv} {future : BlockChain} {a : Adr}
    (trace : MidHistoryTraceIn HistFork mainnetChainConfig start future)
    {tip : Block} (last : future.blocks.getLast? = some tip)
    (early : tip.header.timestamp < mainnetCancunTimestamp)
    (senders : trace.NoSenderAt a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (empty : start.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.rawFrames, root.sevm.caller ≠ a) ∧
      future.state.getCode a = ByteArray.empty := by
  induction trace generalizing tip with
  | tail block cut =>
    obtain ⟨_, _, _, _, postTip⟩ := stateTransitionUsing_reachedStep block.transition
    have tipEq := Option.some.inj (postTip.symm.trans last)
    have blockEarly : block.block.header.timestamp < mainnetCancunTimestamp := by
      rw [tipEq]
      exact early
    have era := mainnetChainConfig_preCancun_of_timestamp_lt block.forkAt blockEarly
    exact block.tail_callers_and_code_empty_of_disabled cut
      (HistFork.stateGas_none block.forkIn)
      (block.forkIn.delegationDisabled_of_prePrague era.toPrePrague)
      (block.forkIn.header_requestsHash_false_of_prePrague era.toPrePrague)
      senders avoid empty
  | step prior block ih =>
    obtain ⟨_, _, _, ⟨parent, parentEq, parentLt⟩, postTip⟩ :=
      stateTransitionUsing_reachedStep block.transition
    have tipEq := Option.some.inj (postTip.symm.trans last)
    have blockEarly : block.block.header.timestamp < mainnetCancunTimestamp := by
      rw [tipEq]
      exact early
    obtain ⟨priorCallers, middleEmpty⟩ := ih parentEq (Nat.lt_trans parentLt blockEarly)
      senders.1 (fun root member => avoid root (List.mem_append_left _ member)) empty
    obtain ⟨blockCallers, final⟩ := block.callers_and_code_empty_before_cancun blockEarly
      senders.2 (fun root member => avoid root (List.mem_append_right _ member)) middleEmpty
    refine ⟨?_, final⟩
    intro root member
    exact (List.mem_append.mp member).elim (priorCallers root) (blockCallers root)

end Blanc.ExecutionTrace
