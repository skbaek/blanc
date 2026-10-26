import Blanc.Lift.WithdrawalRequest.Creation.Block
import Blanc.Lift.WithdrawalRequest.InhibitedObservations
import Blanc.ExecutionMidHistoryInCallerExclusion

/-!
# A canonical deployment and its actual preactivation history

The data retain the configured block containing deployment, its actual transaction cut,
and the following configured blocks to the checkpoint. The computed prefix begins at that
cut's committed post-state and includes the remainder of the deployment block. Environmental
admission supplies Cancun selections, checked sender exclusions, beacon code and SYSTEM
address conditions; EIP-7002 code and INIT are derived from construction and this same history.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.WithdrawalRequest Blanc.ExecutionTrace

/-- A deployment at an actual transaction position in a configured historical block,
followed by actual configured blocks ending at this checkpoint. Initialization is a
consequence of these executions and the input/environment admission below. -/
structure DeploymentHistory (cfg : ChainConfig) (checkpoint : BlockChain) where
  before : BlockChain
  after : BlockChain
  block : ConfiguredBlockTraceIn HistFork cfg before after
  deployment : Creation.DeploymentCut block
  following : ConfiguredHistoryTraceIn HistFork cfg after checkpoint

namespace DeploymentHistory

/-- The exact post-deployment remainder: suffix transactions and later stages of the
same deployment block, followed by this witness's retained configured history. -/
def «prefix» {cfg : ChainConfig} {checkpoint : BlockChain}
    (history : DeploymentHistory cfg checkpoint) :
    MidHistoryTraceIn HistFork cfg history.deployment.cut.afterBenv checkpoint :=
  (MidHistoryTraceIn.tail history.block history.deployment.cut).append history.following

/-- Explicit preactivation input/environment conditions. Canonical EIP-7002 code and INIT
are absent: construction and retained execution derive them. Beacon code is required only
at later whole-block openings, since the deployment-block suffix has no remaining beacon call.
SYSTEM emptiness is at the actual committed post-deployment boundary. -/
structure Admission {cfg : ChainConfig} {checkpoint : BlockChain}
    (history : DeploymentHistory cfg checkpoint) : Prop where
  forks : history.prefix.AllCancun
  senders : history.prefix.NoSenderAt systemAddress
  beacon : history.prefix.BeaconCodeInstalled
  avoid : ∀ root ∈ history.prefix.rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ systemAddress
  systemEmpty : history.deployment.cut.afterBenv.state.getCode systemAddress = ByteArray.empty

/-- Results tied to one retained deployment and its computed prefix. Transaction identity
comes from the block's decoded list; deployed code/storage come from that transaction's
committed CREATE. The checkpoint facts and empty dynamic-target observation concern the
same suffix-and-following execution, preserving the deployment inhibitor before activation. -/
structure Initialized {cfg : ChainConfig} {checkpoint : BlockChain}
    (history : DeploymentHistory cfg checkpoint) : Prop where
  /-- Every block of this actual preactivation prefix selects Cancun. -/
  prefixCancun : history.prefix.AllCancun
  transactionIdentity : history.deployment.cut.index = history.deployment.position ∧
    history.block.bodyTrace.decodedTxs[history.deployment.position]? =
      some history.deployment.cut.tx
  deployedCode : history.deployment.cut.afterBenv.state.getCode withdrawalRequestPredeployAddress =
    Blanc.withdrawalRequestCode
  deployedStorage : RepresentsStorage
    (history.deployment.cut.afterBenv.state.getStor withdrawalRequestPredeployAddress).get initial
  checkpointCode : checkpoint.state.getCode withdrawalRequestPredeployAddress =
    Blanc.withdrawalRequestCode
  checkpointStorage : RepresentsStorage
    (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial
  noDynamicTargets : history.prefix.settledFrames.flatMap balanceFrameObservation = []
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty

/-- Construction and the actual admitted preactivation prefix produce all initialization
facts together. The deployment-block remainder and later configured blocks are exactly
`history.prefix`; caller exclusion and checkpoint SYSTEM emptiness are derived from its
explicit environmental conditions. -/
theorem initialized {cfg : ChainConfig} {checkpoint : BlockChain}
    (history : DeploymentHistory cfg checkpoint) (admission : history.Admission) :
    history.Initialized := by
  have deployed := history.deployment.initial
  have callerFacts := history.prefix.callers_and_code_empty_cancun
    (ca := withdrawalRequestPredeployAddress) admission.forks admission.senders
    admission.beacon admission.avoid admission.systemEmpty (by decide)
  have callers : history.prefix.FrameAdmitted withdrawalRequestPredeployAddress
      (fun sevm _ => sevm.caller ≠ systemAddress) :=
    (history.prefix.frameAdmitted_iff_rawFrames _ _).2 callerFacts.1
  have preserved := inhibited_mid_history_preservesIn HistFork.neutral
    BodyStageCapabilities.historical history.prefix callers deployed.1 deployed.2
  have observed := inhibited_mid_history_observations HistFork.neutral
    BodyStageCapabilities.historical history.prefix callers deployed.1 deployed.2
  exact {
    prefixCancun := admission.forks
    transactionIdentity := history.deployment.transaction_identity
    deployedCode := deployed.1
    deployedStorage := deployed.2
    checkpointCode := preserved.1
    checkpointStorage := observed.1
    noDynamicTargets := observed.2
    systemEmpty := callerFacts.2
  }

end DeploymentHistory

end Blanc.Lift.WithdrawalRequest
