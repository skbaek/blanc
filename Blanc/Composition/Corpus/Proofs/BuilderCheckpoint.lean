import Blanc.Composition.Corpus.Freeze.BuilderRequest
import Blanc.Lift.BuilderRequest.Deposit.Indexed
import Blanc.Lift.BuilderRequest.Exit.Indexed

/-! # Builder histories from the adopted observed checkpoint

These conditional adapters use the same supplied observation for both contracts'
whole initial storage and code. They authenticate neither the RPC record nor a
joint run, and retain the original clean-history and numerical bounds.
-/

namespace Blanc.Composition.Corpus.Proofs.BuilderCheckpoint

open Jaune Blanc Blanc.Lift.BuilderRequest ChainLink
open Blanc.Composition.BuilderRequestPublic Blanc.Corpus.Freeze.Builder

theorem deployedStart_of_observed
    {expectedStateRoot : B256} {checkpoint : BlockChain}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint) :
    DeployedStart checkpoint := by
  refine ⟨?_, ?_, ?_, ?_, obs.depositStorage, obs.exitStorage⟩
  · change ((checkpoint.state.getStor Deposit.Creation.address).get 0).toNat = 0
    rw [obs.depositStorage]
    rfl
  · change ((checkpoint.state.getStor Deposit.Creation.address).get 1).toNat = 0
    rw [obs.depositStorage]
    rfl
  · change ((checkpoint.state.getStor Deposit.Creation.address).get 3).toNat -
      ((checkpoint.state.getStor Deposit.Creation.address).get 2).toNat = 0
    rw [obs.depositStorage]
    rfl
  · change (checkpoint.state.getStor Exit.Creation.address).get 0 = B256.max
    rw [obs.exitStorage]
    exact Stor.get_set_self _ _ _

theorem codesKept_of_observed
    {expectedStateRoot : B256} {cfg : ChainConfig}
    {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    (kept : KeptHistory cfg checkpoint blocks stop) : CodesKept cfg checkpoint blocks stop :=
  ⟨kept, obs.depositCode, obs.exitCode⟩

theorem systemAbsent_of_observed
    {expectedStateRoot : B256} {checkpoint : BlockChain}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint) :
    SystemCodeAbsent checkpoint := ⟨obs.systemEmpty⟩

theorem depositClean_of_observed
    {expectedStateRoot : B256} {cfg : ChainConfig}
    {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    (kept : KeptHistory cfg checkpoint blocks stop) (clean : HistoryClean blocks)
    (budget : feesPaidAt blocks depositAddr ≤ 2 ^ 256) :
    Deposit.Indexed.Clean cfg checkpoint blocks stop :=
  ⟨kept, obs.depositCode, obs.depositStorage, obs.systemEmpty,
    clean.senders, clean.authorities, clean.creates, budget⟩

theorem exitClean_of_observed
    {expectedStateRoot : B256} {cfg : ChainConfig}
    {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    (kept : KeptHistory cfg checkpoint blocks stop) (clean : HistoryClean blocks)
    (few : (exitSubmitted blocks).length ≤ 2 ^ 64) :
    Exit.Indexed.Clean cfg checkpoint blocks stop :=
  ⟨kept, obs.exitCode, obs.exitStorage, obs.systemEmpty,
    clean.senders, clean.authorities, clean.creates, few⟩

theorem observed_history_chain
    {expectedStateRoot : B256} {cfg : ChainConfig}
    {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    (kept : KeptHistory cfg checkpoint blocks stop) (clean : HistoryClean blocks) :
    (∃ frames : List Deposit.Frame,
      Delivery.Chain Stor.empty frames (stop.state.getStor Deposit.Creation.address) ∧
      Corresponds Deposit.contract frames (History.kept Deposit.Creation.address blocks) ∧
      Delivery.systemOutput frames = delivered 3 blocks) ∧
    (∃ frames : List Exit.Frame,
      Delivery.Chain Exit.deployedStorage frames (stop.state.getStor Exit.Creation.address) ∧
      Corresponds Exit.contract frames (History.kept Exit.Creation.address blocks) ∧
      Delivery.systemOutput frames = delivered 4 blocks) := by
  exact ⟨Deposit.history_chain kept obs.depositCode obs.depositStorage obs.systemEmpty
      clean.senders clean.authorities clean.creates,
    Exit.history_chain kept obs.exitCode obs.exitStorage obs.systemEmpty
      clean.senders clean.authorities clean.creates⟩

theorem observed_history_fifo
    {expectedStateRoot : B256} {cfg : ChainConfig}
    {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (obs : BuilderCheckpointObservation expectedStateRoot checkpoint)
    (kept : KeptHistory cfg checkpoint blocks stop) (clean : HistoryClean blocks)
    (budget : feesPaidAt blocks depositAddr ≤ 2 ^ 256)
    (few : (exitSubmitted blocks).length ≤ 2 ^ 64) :
    Deposit.Indexed.submissions blocks =
      Deposit.Indexed.emissions blocks ++ Deposit.Indexed.remainingQueue stop ∧
    Exit.Indexed.submissions blocks =
      Exit.Indexed.emissions blocks ++ Exit.Indexed.remainingQueue stop := by
  exact ⟨Deposit.Indexed.history_fifo (depositClean_of_observed obs kept clean budget),
    Exit.Indexed.history_fifo (exitClean_of_observed obs kept clean few)⟩

theorem b_s4_at (expectedStateRoot : B256) : B_S4_at expectedStateRoot := by
  constructor
  · intro cfg checkpoint stop blocks obs kept clean budget few
    exact history_delivers_bridge (codesKept_of_observed obs kept)
      (deployedStart_of_observed obs) clean (systemAbsent_of_observed obs) budget few
  · intro checkpoint obs
    exact ⟨obs.systemEmpty, obs.depositCode, obs.depositStorage, obs.exitCode, obs.exitStorage⟩

theorem b_s4 : B_S4 := fun expectedStateRoot => b_s4_at expectedStateRoot

end Blanc.Composition.Corpus.Proofs.BuilderCheckpoint
