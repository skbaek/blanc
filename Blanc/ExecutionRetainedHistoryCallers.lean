import Blanc.ExecutionRetainedMessageCallers
import Blanc.ExecutionMidHistoryPreCancunCallers

/-!
# Retained caller exclusion through original pre-Cancun histories

Complete settlement determines the creation obligations. Disabled system stages
contribute no frames; transaction cleanup, withdrawals and rewards preserve
empty code. Initial empty code and actual retained creation avoidance remain
independent lifetime premises.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- A transaction suffix carries the retained-only result through actual
post-transaction settlement when requests and delegation are disabled. -/
theorem ConfiguredBlockTraceIn.tail_retained_callers_and_code_empty_of_disabled
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain} {a : Adr}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (stateGas : block.fork.ruleSet.stateGas = none)
    (delegation : block.fork.ruleSet.delegationEnabled = false)
    (requestsDisabled : block.fork.ruleSet.header.requestsHash = false)
    (senders : cut.after.NoSenderAt a)
    (avoid : ∀ root ∈ (MidHistoryTraceIn.tail block cut).settledFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (empty : cut.afterBenv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ (MidHistoryTraceIn.tail block cut).settledFrames, root.sevm.caller ≠ a) ∧
      post.state.getCode a = ByteArray.empty := by
  have requests := block.bodyTrace.requests.settledFrames_of_disabled requestsDisabled
  simp only [MidHistoryTraceIn.settledFrames, requests, List.append_nil] at avoid ⊢
  have cutSg : cut.afterBenv.stat.rules.stateGas = none := by
    rw [block.txSplit_stat cut]
    exact stateGas
  have cutDelegation : cut.afterBenv.stat.rules.delegationEnabled = false := by
    rw [block.txSplit_stat cut]
    exact delegation
  obtain ⟨finalTx, callers⟩ := cut.after.codeAt_callers_retained_of_disabled
    cutSg cutDelegation senders empty avoid
  refine ⟨callers, ?_⟩
  have afterTx := block.bodyTrace.afterTransactions_codeAt_noStateGas
    (a := a) (by
      rw [block.bodyTrace.transactions.stat_eq]
      exact stateGas) (by
      intro root member
      rw [block.bodyTrace.requests.rawFrames_of_disabled requestsDisabled] at member
      cases member)
  rw [block.postEq]
  exact afterTx.trans finalTx

/-- A whole pre-Cancun block excludes callers in its retained frames using
only retained creation avoidance. Protocol-stage absence comes from its fork. -/
theorem ConfiguredBlockTraceIn.retained_callers_and_code_empty_before_cancun
    {pre post : BlockChain} {a : Adr}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (early : block.block.header.timestamp < mainnetCancunTimestamp)
    (senders : block.bodyTrace.transactions.NoSenderAt a)
    (avoid : ∀ root ∈ block.settledFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (empty : pre.state.getCode a = ByteArray.empty) :
    (∀ root ∈ block.settledFrames, root.sevm.caller ≠ a) ∧
      post.state.getCode a = ByteArray.empty := by
  have era := mainnetChainConfig_preCancun_of_timestamp_lt block.forkAt early
  have disabled := block.systemStagesDisabled_of_mainnet_timestamp_lt early
  have frames : block.settledFrames = block.bodyTrace.transactions.settledFrames := by
    simp only [ConfiguredBlockTraceIn.settledFrames, StagedBodyTrace.settledFrames,
      block.bodyTrace.beacon.settledFrames_of_disabled disabled.1,
      block.bodyTrace.history.settledFrames_of_disabled disabled.2.1,
      block.bodyTrace.requests.settledFrames_of_disabled disabled.2.2,
      List.nil_append, List.append_nil]
  have stateEq : block.bodyTrace.historyState = pre.state :=
    (block.bodyTrace.history.disabled_endpoints disabled.2.1).1.trans
      (block.bodyTrace.beacon.disabled_endpoints disabled.1).1
  obtain ⟨finalTx, callers⟩ := block.bodyTrace.transactions.codeAt_callers_retained_of_disabled
    (HistFork.stateGas_none block.forkIn)
    (block.forkIn.delegationDisabled_of_prePrague era.toPrePrague) senders
    (by change block.bodyTrace.historyState.getCode a = ByteArray.empty; rw [stateEq]; exact empty)
    (by simpa only [frames] using avoid)
  refine ⟨?_, ?_⟩
  · rw [frames]; exact callers
  · have afterTx := block.bodyTrace.afterTransactions_codeAt_noStateGas
      (a := a) (by
        rw [block.bodyTrace.transactions.stat_eq]
        exact HistFork.stateGas_none block.forkIn) (by
        intro root member
        rw [block.bodyTrace.requests.rawFrames_of_disabled disabled.2.2] at member
        cases member)
    rw [block.postEq]
    exact afterTx.trans finalTx

/-- Accepted final-tip chronology supplies the era of every earlier block.
The result follows the original cut and retained forest, including complete
constructor settlement, without restricting any discarded subtree. -/
theorem MidHistoryTraceIn.retained_callers_and_code_empty_before_cancun
    {start : Benv} {future : BlockChain} {a : Adr}
    (trace : MidHistoryTraceIn HistFork mainnetChainConfig start future)
    {tip : Block} (last : future.blocks.getLast? = some tip)
    (early : tip.header.timestamp < mainnetCancunTimestamp)
    (senders : trace.NoSenderAt a)
    (avoid : ∀ root ∈ trace.settledFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (empty : start.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.settledFrames, root.sevm.caller ≠ a) ∧
      future.state.getCode a = ByteArray.empty := by
  induction trace generalizing tip with
  | tail block cut =>
    obtain ⟨_, _, _, _, postTip⟩ := stateTransitionUsing_reachedStep block.transition
    have tipEq := Option.some.inj (postTip.symm.trans last)
    have blockEarly : block.block.header.timestamp < mainnetCancunTimestamp := by
      rw [tipEq]
      exact early
    have era := mainnetChainConfig_preCancun_of_timestamp_lt block.forkAt blockEarly
    exact block.tail_retained_callers_and_code_empty_of_disabled cut
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
    obtain ⟨blockCallers, final⟩ := block.retained_callers_and_code_empty_before_cancun blockEarly
      senders.2 (fun root member => avoid root (List.mem_append_right _ member)) middleEmpty
    refine ⟨?_, final⟩
    intro root member
    exact (List.mem_append.mp member).elim (priorCallers root) (blockCallers root)

end Blanc.ExecutionTrace
