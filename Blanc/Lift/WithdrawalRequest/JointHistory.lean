import Blanc.JointHistory
import Blanc.Lift.WithdrawalRequest.HistoryFifo

/-!
# Valid joint chains for EIP-7002

A valid joint chain is a deployment-rooted configured execution history to an anchor, a joint
run from that anchor, the anchor invariant, the two preset premises, and the trace-wide
execution premises of `history_fifo` stated over the joint history `run.toExec pre`. Nothing
is hidden: every premise is a field.

The anchor invariant is a parameter, `AnchorInv : ∀ {f}, BeaconState P f → Prop`, so the
consensus-side invariant (Jaune `JauneConsensus/Facts/AnchorInv.lean`) plugs in unchanged.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus ExecutionTrace

/-- A valid joint chain from a deployment-rooted checkpoint, through `anchor`, to `final`. -/
structure ValidJoint {P : Preset} (AnchorInv : ∀ {f : CFork}, BeaconState P f → Prop)
    (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (checkpoint : BlockChain)
    (anchor final : JointState P) : Type where
  /-- The canonical deployment and its preactivation history to the checkpoint. -/
  deployment : DeploymentHistory cfg checkpoint
  admission : deployment.Admission
  /-- The configured execution history from the checkpoint to the anchor's execution chain. -/
  pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec
  /-- The joint run from the anchor. -/
  run : JointRun cfg ccfg bls anchor final
  /-- The anchor invariant on the anchor's beacon state. -/
  anchorInv : AnchorInv anchor.beacon
  slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH
  activationBalance : P.MIN_ACTIVATION_BALANCE ≤ P.MAX_EFFECTIVE_BALANCE_ELECTRA
  otherInstalled : OtherSystemCodeInstalled checkpoint.state
  senders : (run.toExec pre).NoSenderAt systemAddress
  authorities : (run.toExec pre).NoAuthorityAt systemAddress
  /-- No CREATE frame targets `SYSTEM_ADDRESS`. -/
  avoid : ∀ root ∈ (run.toExec pre).rawFrames,
    root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress
  occurrences : (submissions (run.toExec pre)).length ≤ wordOccurrenceCap

/-- The joint history of a valid joint chain: the pre-anchor history extended by the run. -/
noncomputable abbrev ValidJoint.history {P : Preset} {AnchorInv : ∀ {f : CFork}, BeaconState P f → Prop}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint AnchorInv cfg ccfg bls checkpoint anchor final) :
    ConfiguredHistoryTrace cfg checkpoint final.exec :=
  v.run.toExec v.pre

/-- The EIP-7002 FIFO along a valid joint chain's joint history, by `history_fifo` unchanged. -/
theorem ValidJoint.history_fifo {P : Preset} {AnchorInv : ∀ {f : CFork}, BeaconState P f → Prop}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint AnchorInv cfg ccfg bls checkpoint anchor final) :
    HistoryFifo (v.run.toExec v.pre) :=
  Blanc.Lift.WithdrawalRequest.history_fifo v.deployment v.admission (v.run.toExec v.pre)
    v.otherInstalled v.senders v.authorities v.avoid v.occurrences

end Blanc.Lift.WithdrawalRequest
