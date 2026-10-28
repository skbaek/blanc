import Blanc.Composition.LiveUsdcWeth9B26213219PrePairCallers
import Blanc.ExecutionHistoryInReached

/-!
# Exact block binding for the supplied finite checkpoint

The generated block coordinates are tied to the actual final tip of the same
chain whose state supplies the observations and deployment histories. These
equalities are an explicit fetched-data boundary, not a consensus or state-root
authentication theorem. No observation is adopted by defining this interface.
Future traces retain the supplied bodies, frames and checked sender queries.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- The actual history endpoint and its finite reads name the same frozen B.
The state-root equality names the observed header field; it does not assert
that recomputing a trie over the supplied world yields that root. -/
structure ObservedCheckpoint (checkpoint : BlockChain) where
  tip : Block
  last : checkpoint.blocks.getLast? = some tip
  chain : checkpoint.chainId.toNat = LiveUsdcWeth9B26213219Data.chainId
  number : tip.header.number = LiveUsdcWeth9B26213219Data.blockNumber
  timestamp : tip.header.timestamp = LiveUsdcWeth9B26213219Data.blockTimestamp
  hash : tip.header.hash = LiveUsdcWeth9B26213219Data.blockHash
  stateRoot : tip.header.stateRoot = LiveUsdcWeth9B26213219Data.stateRoot
  reads : ObservedAt checkpoint.state

/-- The generated coordinates select BPO2 in the pinned mainnet schedule. -/
theorem frozen_fork :
    mainnetChainConfig.forkAt LiveUsdcWeth9B26213219Data.blockNumber LiveUsdcWeth9B26213219Data.blockTimestamp = .ok .bpo2 := by
  decide +kernel

/-- The starting timestamp already lies in the existing covered-fork domain. -/
theorem frozen_prague_floor : mainnetPragueTimestamp ≤ LiveUsdcWeth9B26213219Data.blockTimestamp := by
  decide +kernel

/-- The bound checkpoint selects the recorded fork without an extra fork premise. -/
theorem ObservedCheckpoint.fork {checkpoint : BlockChain}
    (anchor : ObservedCheckpoint checkpoint) :
    mainnetChainConfig.forkAt anchor.tip.header.number anchor.tip.header.timestamp =
      .ok .bpo2 := by
  rw [anchor.number, anchor.timestamp]
  exact frozen_fork

/-- The exact original tip supplies the future-history timestamp floor. -/
theorem ObservedCheckpoint.tip_floor {checkpoint : BlockChain}
    (anchor : ObservedCheckpoint checkpoint) :
    ∃ tip, checkpoint.blocks.getLast? = some tip ∧ LiveUsdcWeth9B26213219Data.blockTimestamp ≤ tip.header.timestamp :=
  ⟨anchor.tip, anchor.last, anchor.timestamp ▸ Nat.le_refl _⟩

/-- Every successful future selection after the frozen timestamp is covered.
This is a fact about the pinned schedule, not unspecified future fork semantics. -/
theorem covered_after_frozen (number timestamp : Nat) (fork : Fork)
    (after : LiveUsdcWeth9B26213219Data.blockTimestamp ≤ timestamp)
    (selected : mainnetChainConfig.forkAt number timestamp = .ok fork) : CoveredFork fork :=
  mainnetChainConfig_covered number timestamp fork
    (Nat.le_trans frozen_prague_floor after) selected

/-- Convert the supplied future history, preserving its original execution
evidence. There is no extraction of another history from endpoint reachability. -/
def ObservedCheckpoint.futureTrace {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (trace : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future) :
    ConfiguredHistoryTrace mainnetChainConfig checkpoint future :=
  (trace.coveredOfReached LiveUsdcWeth9B26213219Data.blockTimestamp covered_after_frozen anchor.tip_floor).toModern

/-- The original raw frames, including failed executions, remain unchanged. -/
theorem ObservedCheckpoint.futureTrace_rawFrames {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (trace : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future) :
    (anchor.futureTrace trace).rawFrames = trace.rawFrames := by
  unfold futureTrace
  rw [ConfiguredHistoryTraceIn.toModern_rawFrames,
    ConfiguredHistoryTraceIn.coveredOfReached_rawFrames]

/-- The original complete-settlement forest remains unchanged. -/
theorem ObservedCheckpoint.futureTrace_settledFrames {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (trace : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future) :
    (anchor.futureTrace trace).settledFrames = trace.settledFrames := by
  unfold futureTrace
  rw [ConfiguredHistoryTraceIn.toModern_settledFrames,
    ConfiguredHistoryTraceIn.coveredOfReached_settledFrames]

/-- Checked sender occurrences retain exact order and original admission evidence. -/
theorem ObservedCheckpoint.futureTrace_senderOccurrences {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (trace : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future) :
    (anchor.futureTrace trace).senderOccurrences = trace.senderOccurrences := by
  unfold futureTrace
  rw [ConfiguredHistoryTraceIn.toModern_senderOccurrences,
    ConfiguredHistoryTraceIn.coveredOfReached_senderOccurrences]

/-- Failed transactions and repeated recovery queries are not filtered away. -/
theorem ObservedCheckpoint.futureTrace_senderQueries {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (trace : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future) :
    (anchor.futureTrace trace).senderQueries = trace.senderQueries := by
  unfold futureTrace
  rw [ConfiguredHistoryTraceIn.toModern_senderQueries,
    ConfiguredHistoryTraceIn.coveredOfReached_senderQueries]

/-- Accepted future blocks cannot move the actual tip before the frozen block's
timestamp, including a reflexive continuation. -/
theorem ObservedCheckpoint.future_tip_floor {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (trace : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future) :
    ∃ tip, future.blocks.getLast? = some tip ∧ LiveUsdcWeth9B26213219Data.blockTimestamp ≤ tip.header.timestamp :=
  trace.toReachUsing.tip_floor anchor.tip_floor

/-- The checkpoint theorem consumes finite reads bound to the actual B tip.
Initial Pair code and retained creation provenance remain separate obligations;
the binding does not manufacture either history or an allowance seed. -/
theorem checkpoint_at_bound_deployment_model {checkpoint : BlockChain}
    (anchor : ObservedCheckpoint checkpoint) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initial : wd.cut.afterBenv.state.getCode pair = ByteArray.empty) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys pd.keys
      pd.model checkpoint.state :=
  checkpoint_at_deployment_model_of_retained_lifetime anchor.reads wd pd link
    holderFresh excluded avoid initial

/-- The bound checkpoint from absence of Pair-owned WETH approvals in the
original receipts before Pair deployment. The receipt predicate remains an
explicit premise; this theorem adopts no external observation. -/
theorem checkpoint_at_bound_deployment_model_of_receipts {checkpoint : BlockChain}
    (anchor : ObservedCheckpoint checkpoint) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        link.beforePairReceiptLogs) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys pd.keys
      pd.model checkpoint.state :=
  checkpoint_at_deployment_model anchor.reads wd pd link holderFresh excluded logs

end Blanc.Composition.LiveUsdcWeth9B26213219
