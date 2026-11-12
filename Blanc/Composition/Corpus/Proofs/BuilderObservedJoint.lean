import Blanc.Composition.Corpus.Proofs.BuilderCheckpoint
import Blanc.Composition.BuilderRequestJointG

/-! # The adopted builder checkpoint on the original joint carrier

The observation supplies five checkpoint fields. Every other joint input is
explicit and unchanged; the actual spliced kept history supplies code coverage.
This constructs no joint run from the observation and changes no BLS parameter.
-/

namespace Blanc.Composition.Corpus.Proofs.BuilderObservedJoint

open Jaune JauneConsensus Blanc Blanc.Lift.BuilderRequest ChainLink
open Blanc.Composition.BuilderRequestPublic Blanc.Corpus.Freeze.Builder
open Blanc.Composition.Corpus.Proofs.BuilderCheckpoint

/-- The existing joint bundle at the same observed checkpoint, with all remaining inputs explicit. -/
noncomputable def joint_of_observed
    {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {expectedStateRoot : B256} {checkpoint : BlockChain} {anchor final : GJointState P}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    (preBlocks : List KeptBlock)
    (prefixHistory : KeptHistory cfg checkpoint preBlocks anchor.exec)
    (run : GJointRun cfg ccfg bls anchor final)
    (anchorPending : AnchorPendingTrace cfg ccfg bls anchor)
    (anchorInv : GAnchorInv anchor)
    (anchorWitness : AnchorBidWitness anchor)
    (anchorJoint : GJointInv cfg anchor)
    (senders : History.NoSender systemAddress (preBlocks ++ run.blocks))
    (authorities : History.NoAuthority systemAddress (preBlocks ++ run.blocks))
    (creates : History.NoCreate systemAddress (preBlocks ++ run.blocks))
    (depositBudget : History.paid Deposit.Creation.address (preBlocks ++ run.blocks) ≤ 2 ^ 256)
    (exitFew : (History.submitted Exit.contract (preBlocks ++ run.blocks)).length ≤ 2 ^ 64)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (inclusionDelay : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY)
    (exitDelayPos : 0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY)
    (exitDelayBelow : ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY < 2 ^ 63)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (validatorsBound : ∀ st ∈ run.states, st.validatorCount ≤ 2 ^ 40)
    (buildersBound : ∀ st ∈ run.states, st.builderCount ≤ 2 ^ 40)
    (roots : HistoryRootsFit (preBlocks ++ run.blocks))
    (depositNoSender : History.NoSender depositAddr (preBlocks ++ run.blocks))
    (exitNoSender : History.NoSender exitAddr (preBlocks ++ run.blocks))
    (creditsFit : HistoryCreditsFit depositAddr (preBlocks ++ run.blocks) ∧
    HistoryCreditsFit exitAddr (preBlocks ++ run.blocks))
    : ValidJointG cfg ccfg bls checkpoint anchor final where
  noSystemCode := obs.systemEmpty
  preBlocks := preBlocks
  prefixHistory := prefixHistory
  run := run
  anchorPending := anchorPending
  anchorInv := anchorInv
  anchorWitness := anchorWitness
  anchorJoint := anchorJoint
  depositInstalled := obs.depositCode
  depositFresh := obs.depositStorage
  exitInstalled := obs.exitCode
  exitFresh := obs.exitStorage
  senders := senders
  authorities := authorities
  creates := creates
  depositBudget := depositBudget
  exitFew := exitFew
  quorumPositive := quorumPositive
  inclusionDelay := inclusionDelay
  exitDelayPos := exitDelayPos
  exitDelayBelow := exitDelayBelow
  slotsPerEpoch := slotsPerEpoch
  validatorsBound := validatorsBound
  buildersBound := buildersBound
  roots := roots
  depositNoSender := depositNoSender
  exitNoSender := exitNoSender
  creditsFit := creditsFit
  codes := ⟨prefixHistory.append run.keptHistory, obs.depositCode, obs.exitCode⟩

/-- Both actual whole-storage frame chains of this same-checkpoint joint history. -/
theorem joint_history_chain
    {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {expectedStateRoot : B256} {checkpoint : BlockChain} {anchor final : GJointState P}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    (preBlocks : List KeptBlock)
    (prefixHistory : KeptHistory cfg checkpoint preBlocks anchor.exec)
    (run : GJointRun cfg ccfg bls anchor final)
    (anchorPending : AnchorPendingTrace cfg ccfg bls anchor)
    (anchorInv : GAnchorInv anchor)
    (anchorWitness : AnchorBidWitness anchor)
    (anchorJoint : GJointInv cfg anchor)
    (senders : History.NoSender systemAddress (preBlocks ++ run.blocks))
    (authorities : History.NoAuthority systemAddress (preBlocks ++ run.blocks))
    (creates : History.NoCreate systemAddress (preBlocks ++ run.blocks))
    (depositBudget : History.paid Deposit.Creation.address (preBlocks ++ run.blocks) ≤ 2 ^ 256)
    (exitFew : (History.submitted Exit.contract (preBlocks ++ run.blocks)).length ≤ 2 ^ 64)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (inclusionDelay : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY)
    (exitDelayPos : 0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY)
    (exitDelayBelow : ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY < 2 ^ 63)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (validatorsBound : ∀ st ∈ run.states, st.validatorCount ≤ 2 ^ 40)
    (buildersBound : ∀ st ∈ run.states, st.builderCount ≤ 2 ^ 40)
    (roots : HistoryRootsFit (preBlocks ++ run.blocks))
    (depositNoSender : History.NoSender depositAddr (preBlocks ++ run.blocks))
    (exitNoSender : History.NoSender exitAddr (preBlocks ++ run.blocks))
    (creditsFit : HistoryCreditsFit depositAddr (preBlocks ++ run.blocks) ∧
    HistoryCreditsFit exitAddr (preBlocks ++ run.blocks))
    : (∃ frames : List Deposit.Frame,
        Delivery.Chain Stor.empty frames (final.exec.state.getStor Deposit.Creation.address) ∧
        Corresponds Deposit.contract frames
          (History.kept Deposit.Creation.address (preBlocks ++ run.blocks)) ∧
        Delivery.systemOutput frames = delivered 3 (preBlocks ++ run.blocks)) ∧
      (∃ frames : List Exit.Frame,
        Delivery.Chain Exit.deployedStorage frames (final.exec.state.getStor Exit.Creation.address) ∧
        Corresponds Exit.contract frames
          (History.kept Exit.Creation.address (preBlocks ++ run.blocks)) ∧
        Delivery.systemOutput frames = delivered 4 (preBlocks ++ run.blocks)) := by
  let v := joint_of_observed obs preBlocks prefixHistory run anchorPending anchorInv anchorWitness anchorJoint senders authorities creates depositBudget exitFew quorumPositive inclusionDelay exitDelayPos exitDelayBelow slotsPerEpoch validatorsBound buildersBound roots depositNoSender exitNoSender creditsFit
  exact observed_history_chain obs v.keptHistory ⟨v.senders, v.authorities, v.creates⟩

/-- Both output-record FIFO equalities, including the actual final stored remainders. -/
theorem joint_history_fifo
    {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {expectedStateRoot : B256} {checkpoint : BlockChain} {anchor final : GJointState P}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    (preBlocks : List KeptBlock)
    (prefixHistory : KeptHistory cfg checkpoint preBlocks anchor.exec)
    (run : GJointRun cfg ccfg bls anchor final)
    (anchorPending : AnchorPendingTrace cfg ccfg bls anchor)
    (anchorInv : GAnchorInv anchor)
    (anchorWitness : AnchorBidWitness anchor)
    (anchorJoint : GJointInv cfg anchor)
    (senders : History.NoSender systemAddress (preBlocks ++ run.blocks))
    (authorities : History.NoAuthority systemAddress (preBlocks ++ run.blocks))
    (creates : History.NoCreate systemAddress (preBlocks ++ run.blocks))
    (depositBudget : History.paid Deposit.Creation.address (preBlocks ++ run.blocks) ≤ 2 ^ 256)
    (exitFew : (History.submitted Exit.contract (preBlocks ++ run.blocks)).length ≤ 2 ^ 64)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (inclusionDelay : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY)
    (exitDelayPos : 0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY)
    (exitDelayBelow : ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY < 2 ^ 63)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (validatorsBound : ∀ st ∈ run.states, st.validatorCount ≤ 2 ^ 40)
    (buildersBound : ∀ st ∈ run.states, st.builderCount ≤ 2 ^ 40)
    (roots : HistoryRootsFit (preBlocks ++ run.blocks))
    (depositNoSender : History.NoSender depositAddr (preBlocks ++ run.blocks))
    (exitNoSender : History.NoSender exitAddr (preBlocks ++ run.blocks))
    (creditsFit : HistoryCreditsFit depositAddr (preBlocks ++ run.blocks) ∧
    HistoryCreditsFit exitAddr (preBlocks ++ run.blocks))
    : Deposit.Indexed.submissions (preBlocks ++ run.blocks) =
        Deposit.Indexed.emissions (preBlocks ++ run.blocks) ++
          Deposit.Indexed.remainingQueue final.exec ∧
      Exit.Indexed.submissions (preBlocks ++ run.blocks) =
        Exit.Indexed.emissions (preBlocks ++ run.blocks) ++
          Exit.Indexed.remainingQueue final.exec := by
  let v := joint_of_observed obs preBlocks prefixHistory run anchorPending anchorInv anchorWitness anchorJoint senders authorities creates depositBudget exitFew quorumPositive inclusionDelay exitDelayPos exitDelayBelow slotsPerEpoch validatorsBound buildersBound roots depositNoSender exitNoSender creditsFit
  exact observed_history_fifo obs v.keptHistory ⟨v.senders, v.authorities, v.creates⟩
    v.depositBudget v.exitFew

end Blanc.Composition.Corpus.Proofs.BuilderObservedJoint
