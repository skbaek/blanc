import Blanc.Lift.BeaconDeposit.HistCommittedHistory
import Blanc.ExecutionHistoryInSystemEnvironment
import Blanc.ExecutionHistoryInWarmth
import Blanc.ExecutionHistoryInCodeAt
import Blanc.ExecutionStagedFrameEnv
import Blanc.ExecutionHistoryInCreateAvoid

/-! Historical committed-history headlines with derived frame environments.
System installations are explicit at actual block openings, selected by fork:
none at D before Cancun; beacon roots at Cancun; the canonical set from Prague.
No frame can CREATE at an installed system contract: the present code collides.
Seam composition must derive those opening inputs from the accepted C/P anchors. -/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace

private theorem block_beaconEntry_of_envIn {ca : Adr} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn HistFork cfg pre post)
    (systemInstalled : trace.SystemCodeAtOpening)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.PragueNoAuthorityAt p.1)
    (systemNoFrame : trace.InstalledNoFrame)
    (checkpointEmpty : pre.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.PragueNoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (installed : pre.state.getCode ca = code) :
    trace.FrameAdmitted ca beaconEntry ∧ post.state.getCode 2 = ByteArray.empty := by
  have hdis : trace.fork.ruleSet.delegationEnabled = false ∨
      ∀ q ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ q.2.auths,
        ∀ authority, recoverAuthority auth = .ok authority → authority ≠ (2 : Adr) := by
    by_cases hpre : PrePrague trace.fork
    · exact Or.inl (trace.forkIn.delegationDisabled_of_prePrague hpre)
    · exact Or.inr (noAuthority hpre)
  obtain ⟨emptyFrames, emptyPost⟩ := trace.codeAt_empty_noStateGas
    BodyStageCapabilities.historical hdis noFrame checkpointEmpty
  have hsize : code.size = 6358 := by
    rw [ByteArray.size_eq_length_toList]
    exact code_toList_length
  have notSystem : ca ∉ (installedAt trace.fork).map Prod.fst :=
    not_mem_installedAt_of_size trace.forkIn installed systemInstalled (by
      intro p hp
      rw [hsize]
      simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide +kernel)
  have systemTargets := trace.systemFrames_target_of_installedAt trace.forkIn systemInstalled
    systemNoAuthority systemNoFrame
  refine ⟨?_, emptyPost⟩
  rw [trace.frameAdmitted_iff_rawFrames]
  intro root member target
  rcases trace.rawFrames_system_or_tx root member with hsys | htx
  · exact (notSystem (target ▸ systemTargets root hsys)).elim
  · refine ⟨trace.calldata_bound BodyStageCapabilities.historical
      (fun _ hf => hf.dataNonZero_ge) root member, ?_, ?_⟩
    · show getDelegatedCodeAddress (root.devm.getCode 2) = none
      rw [emptyFrames root htx]
      rfl
    · exact trace.transactions_rawFrames_warmIn BodyStageCapabilities.historical
        (fun _ hf => hf.two_mem_precompiles) root htx

/-- Admission and code-at-2 are derived together with preservation of the Beacon invariant.
Each induction step uses the preceding actual state to distinguish the active system targets. -/
private theorem historicalEnvironment {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (systemInstalled : trace.SystemCodeAtOpenings)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.PragueNoAuthorityAt p.1)
    (systemNoFrame : trace.InstalledNoFrame)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.PragueNoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (rewards : trace.RewardCreditsFunded)
    (initial : beaconSpec.StateInv ca checkpoint.state) :
    trace.FrameAdmitted ca beaconEntry ∧ beaconSpec.StateInv ca future.state ∧
      future.state.getCode 2 = ByteArray.empty := by
  induction trace with
  | refl => exact ⟨trivial, initial, checkpointEmpty⟩
  | step prior block ih =>
      obtain ⟨priorAdmission, priorInv, priorEmpty⟩ := ih systemInstalled.1
        (fun p hp => (systemNoAuthority p hp).1)
        systemNoFrame.1
        noAuthority.1
        (fun root member => noFrame root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inl member))
        rewards.1
      have priorInstalled := ContractSpecSem.StateInv.getCode_eq_of_image
        (C := code) rfl priorInv
      obtain ⟨blockAdmission, blockEmpty⟩ := block_beaconEntry_of_envIn block systemInstalled.2
        (fun p hp => (systemNoAuthority p hp).2)
        systemNoFrame.2
        priorEmpty noAuthority.2
        (fun root member => noFrame root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inr member))
        priorInstalled
      have blockInv := block.stateInv_admitted_semIn (beaconSpec_preservesAdmittedIn ca)
        BodyStageCapabilities.historical ((block.freshFrameAdmitted ca).and blockAdmission)
        rewards.2 priorInv beaconInstalledCertH rfl
      exact ⟨⟨priorAdmission, blockAdmission⟩, blockInv, blockEmpty⟩

/-- Derived admission, endpoint invariant and empty precompile code for downstream seams. -/
theorem configuredHistoryIn_environment {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (systemInstalled : trace.SystemCodeAtOpenings)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.PragueNoAuthorityAt p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.PragueNoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (rewards : trace.RewardCreditsFunded)
    (initial : beaconSpec.StateInv ca checkpoint.state) :
    trace.FrameAdmitted ca beaconEntry ∧ beaconSpec.StateInv ca future.state ∧
      future.state.getCode 2 = ByteArray.empty :=
  historicalEnvironment trace systemInstalled systemNoAuthority
    (trace.installedNoFrame_of_openings systemInstalled systemNoAuthority)
    checkpointEmpty noAuthority noFrame rewards initial

/-- The final historical headline has no per-frame admission, calldata, warmth or delegation
premise. The only system-code input is the selected era's actual block-opening installation. -/
theorem configuredHistoryIn_solInv {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (systemInstalled : trace.SystemCodeAtOpenings)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.PragueNoAuthorityAt p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.PragueNoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ (2 : Adr))
    (rewards : trace.RewardCreditsFunded)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodesIn ca trace) := by
  have initial : beaconSpec.StateInv ca checkpoint.state :=
    ⟨by rw [installed]; rfl, trivial, ⟨initialHistory, invariant⟩⟩
  obtain ⟨admitted, -, -⟩ := historicalEnvironment trace systemInstalled systemNoAuthority
    (trace.installedNoFrame_of_openings systemInstalled systemNoAuthority) checkpointEmpty
    noAuthority noFrame rewards initial
  exact configuredHistoryIn_solInv_admitted trace admitted rewards installed invariant

end Blanc.Lift.BeaconDeposit

