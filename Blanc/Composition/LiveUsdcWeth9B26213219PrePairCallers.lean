import Blanc.Composition.LiveUsdcWeth9B26213219AllowanceReplay
import Blanc.ExecutionRetainedHistoryCallers

/-!
# Structural caller provenance strictly before the genuine Pair creation

The original admitted sender queries supply keylessness; accepted block
chronology supplies the pre-Cancun capability scope. Initial empty Pair code
and absence of retained Pair creations in this earlier interval remain explicit
lifetime obligations. Empty code at the later deployment cut does not prove
them. No historical observation or absence assumption is adopted here.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The exact raw entries before createPair, excluding the creation transaction. -/
def DeploymentHistoryLink.beforePairRawFrames {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) : List Exec.Deriv :=
  link.earlierTrace.rawFrames ++ pd.cut.before.rawFrames

/-- All earlier sender queries come from the original WETH deployment history,
including transactions whose VM execution later fails. -/
theorem DeploymentHistoryLink.beforePairQueries_subset {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd) :
    link.earlierTrace.senderQueries ++ pd.cut.before.senderQueries ⊆ wd.trace.senderQueries := by
  intro query member
  change query ∈ ((MidHistoryTraceIn.tail wd.block wd.cut).append wd.history).senderQueries
  rw [MidHistoryTraceIn.append_senderQueries, link.history,
    ConfiguredHistoryTraceIn.append_senderQueries]
  have step : (link.between.step pd.block).senderQueries =
      link.between.senderQueries ++ pd.block.bodyTrace.transactions.senderQueries :=
    List.map_append
  rw [step]
  simp only [earlierTrace, MidHistoryTraceIn.append_senderQueries, List.mem_append] at member
  rcases member with (tail | middle) | before
  · exact List.mem_append_left _ tail
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ middle))
  · rw [pd.cut.senderQueries_before] at before
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_of_mem_take before)))

/-- The caller conclusion for every original retained pre-Pair frame follows
from the separate lifetime obligations and original sender-query exclusion. -/
theorem DeploymentHistoryLink.beforePair_callers_of_retained_lifetime {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initial : wd.cut.afterBenv.state.getCode pair = ByteArray.empty) :
    ∀ G ∈ link.beforePairFrames, G.sevm.caller ≠ pair := by
  have early : pd.block.block.header.timestamp < mainnetCancunTimestamp := by
    rw [pd.time]
    decide +kernel
  obtain ⟨_, _, _, ⟨parent, parentEq, parentLt⟩, _⟩ :=
    stateTransitionUsing_reachedStep pd.block.transition
  have earlierSenders := link.earlierTrace.noSenderAt_of_senderQueries
    (fun query member => excluded query (link.beforePairQueries_subset
      (List.mem_append_left _ member)))
  obtain ⟨earlierCallers, emptyPre⟩ := link.earlierTrace.retained_callers_and_code_empty_before_cancun
    parentEq (Nat.lt_trans parentLt early) earlierSenders
    (fun root member => avoid root (List.mem_append_left _ member)) initial
  have disabled := pd.block.systemStagesDisabled_of_mainnet_timestamp_lt early
  have beacon := pd.block.bodyTrace.beacon.disabled_endpoints disabled.1
  have history := pd.block.bodyTrace.history.disabled_endpoints disabled.2.1
  have stateEq : pd.block.bodyTrace.historyState = pd.pre.state := history.1.trans beacon.1
  have era := mainnetChainConfig_preCancun_of_timestamp_lt pd.block.forkAt early
  have gas : (initBenv pd.block.fork pd.pre pd.block.block.header).stat.rules.stateGas = none :=
    HistFork.stateGas_none pd.block.forkIn
  have delegation : (initBenv pd.block.fork pd.pre pd.block.block.header).stat.rules.delegationEnabled = false :=
    pd.block.forkIn.delegationDisabled_of_prePrague era.toPrePrague
  have prefixAvoid : ∀ root ∈ pd.cut.before.settledFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair :=
    fun root member => avoid root (List.mem_append_right _ member)
  have prefixEmpty : pd.block.bodyTrace.historyState.getCode pair = ByteArray.empty := by
    rw [stateEq]
    exact emptyPre
  have prefixSenders := pd.cut.before.noSenderAt_of_senderQueries
    (fun query member => excluded query (link.beforePairQueries_subset
      (List.mem_append_right _ member)))
  have prefixCallers := (pd.cut.before.codeAt_callers_retained_of_disabled gas
    delegation prefixSenders prefixEmpty prefixAvoid).2
  intro G member
  rcases List.mem_append.mp member with earlier | before
  · exact earlierCallers G earlier
  · exact prefixCallers G before

/-- The caller conclusion for every original retained pre-Pair frame follows
from the separate lifetime obligations and original sender-query exclusion. -/
theorem DeploymentHistoryLink.beforePair_callers_of_lifetime {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairRawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initial : wd.cut.afterBenv.state.getCode pair = ByteArray.empty) :
    ∀ G ∈ link.beforePairFrames, G.sevm.caller ≠ pair := by
  apply link.beforePair_callers_of_retained_lifetime excluded (initial := initial)
  intro root member
  apply avoid (Blanc.Exec.Frame.rootDeriv (frame := root))
  rcases List.mem_append.mp member with earlier | before
  · exact List.mem_append_left _
      (link.earlierTrace.mem_rawFrames_of_mem_settledFrames root earlier)
  · exact List.mem_append_right _
      (pd.cut.before.mem_rawFrames_of_mem_settledFrames root before)

/-- Constructor zero, structural earlier callers, exact creation storage
preservation and later Pair runtime facts jointly prove the tracked zero rows. -/
theorem DeploymentHistoryLink.allowance_zero_of_retained_lifetime {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initial : wd.cut.afterBenv.state.getCode pair = ByteArray.empty) :
    ∀ g, wd.keys (.allow pair g) →
      (checkpoint.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  apply link.allowance_zero_of_before_pair excluded
  intro G member _ caller
  exact (link.beforePair_callers_of_retained_lifetime excluded avoid initial G member caller).elim

/-- Constructor zero, structural earlier callers, exact creation storage
preservation and later Pair runtime facts jointly prove the tracked zero rows. -/
theorem DeploymentHistoryLink.allowance_zero_of_lifetime {checkpoint : BlockChain}
    {wd : WethDeploymentTo checkpoint} {pd : PairDeploymentTo checkpoint}
    (link : DeploymentHistoryLink wd pd)
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairRawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initial : wd.cut.afterBenv.state.getCode pair = ByteArray.empty) :
    ∀ g, wd.keys (.allow pair g) →
      (checkpoint.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  apply link.allowance_zero_of_before_pair excluded
  intro G member _ caller
  exact (link.beforePair_callers_of_lifetime excluded avoid initial G member caller).elim

open Blanc.Composition.UniswapV2PairUsdcWeth9 in
/-- The same historical Pair model yields a hybrid checkpoint from structural
lifetime premises, without a receipt-absence or endpoint allowance premise. -/
theorem checkpoint_at_deployment_model_of_retained_lifetime {checkpoint : BlockChain}
    (reads : ObservedAt checkpoint.state) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initial : wd.cut.afterBenv.state.getCode pair = ByteArray.empty) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys pd.keys
      pd.model checkpoint.state := by
  obtain ⟨sumNof, foot⟩ := wd.foot
  exact checkpoint_of_history reads pd.rep foot sumNof
    (reads.weth_tracked foot holderFresh) (link.allowance_zero_of_retained_lifetime excluded avoid initial)

open Blanc.Composition.UniswapV2PairUsdcWeth9 in
/-- The same historical Pair model yields a hybrid checkpoint from structural
lifetime premises, without a receipt-absence or endpoint allowance premise. -/
theorem checkpoint_at_deployment_model_of_lifetime {checkpoint : BlockChain}
    (reads : ObservedAt checkpoint.state) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairRawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initial : wd.cut.afterBenv.state.getCode pair = ByteArray.empty) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys pd.keys
      pd.model checkpoint.state := by
  obtain ⟨sumNof, foot⟩ := wd.foot
  exact checkpoint_of_history reads pd.rep foot sumNof
    (reads.weth_tracked foot holderFresh) (link.allowance_zero_of_lifetime excluded avoid initial)

end Blanc.Composition.LiveUsdcWeth9B26213219
