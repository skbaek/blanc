import Blanc.Lift.WithdrawalRequest.UserSetup
import Blanc.Lift.WithdrawalRequest.CodeFacts
import Blanc.Lift.WithdrawalRequest.Layout
import Blanc.StorageOnlySpec
import Blanc.ExecutionHistoricalLadder
import Blanc.ExecutionMidHistoryInFacts

/-!
Preservation of the canonical deployment inhibitor through an actual selected-domain
history. Caller exclusion is an explicit intermediate admission obligation.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.WithdrawalRequest Blanc.ExecutionTrace

/-- Only the canonical image is needed by the inhibited-frame proof. -/
def inhibitedSem : CodeSem where
  image := some Blanc.withdrawalRequestCode.toList
  Run sevm _ _ := sevm.code = Blanc.withdrawalRequestCode
  correct := by
    intro sevm pre post execution image
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj image
  ne_nil := by
    intro bytes image
    cases Option.some.inj image
    exact withdrawalRequestCode_sem_facts.2
  not_delegation := by
    intro bytes image
    have eq : bytes = Blanc.withdrawalRequestCode := by
      apply ByteArray.ext
      apply Array.toList_inj.mp
      simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj image
    rw [eq]
    exact withdrawalRequestCode_sem_facts.1

/-- The deployment storage representation, without balance requirements. -/
def inhibitedSpec : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly inhibitedSem (fun storage => RepresentsStorage storage.get initial)

/-- Fresh entry is supplied by frame initialization; caller exclusion remains an
explicit intermediate obligation until the protocol admission producer is applied. -/
def inhibitedEntry (sevm : Sevm) (pre : Devm) : Prop :=
  Exec.FreshEntry sevm pre ∧ sevm.caller ≠ systemAddress

/-- Actual target success contradicts the represented deployment inhibitor. -/
theorem inhibitedSpec_soundIn {F : Fork → Prop}
    (neutral : ∀ {f : Fork}, F f → NeutralFork f) :
    inhibitedSpec.SoundAdmittedIn F withdrawalRequestPredeployAddress inhibitedEntry := by
  intro sevm pre post fork execution code target admitted ih wf invariant
  have entry := admitted.root target
  have rep := ContractSpecSem.ofStorageOnly_preInv_iff.mp invariant.inv
  have inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max := by
    rw [target]
    exact rep.excess
  exact False.elim (exec_user_inhibited_no_okH code (neutral fork).stateGas
    (neutral fork).bal entry.1.1 entry.2 inhibited execution)

/-- The existing historical frame ladder handles foreign code and failed settlement. -/
theorem inhibitedSpec_preservesIn {F : Fork → Prop}
    (neutral : ∀ {f : Fork}, F f → NeutralFork f) :
    inhibitedSpec.PreservesAdmittedIn F withdrawalRequestPredeployAddress inhibitedEntry :=
  ContractSpecSem.preserves_inv_admittedIn F (fun fork => (neutral fork).stateGas)
    inhibitedSpec withdrawalRequestPredeployAddress inhibitedEntry (inhibitedSpec_soundIn neutral)

/-- The canonical checked runtime meets the installed-code transport conditions. -/
theorem inhibitedInstalledCert : InstalledCert Blanc.withdrawalRequestCode := by
  refine ⟨⟨cert, cert_check, ?_, ?_⟩,
    withdrawalRequestCode_sem_facts.1, withdrawalRequestCode_sem_facts.2⟩
  · decide +kernel
  · decide +kernel

/-- Freshness in a mid-block history is derived from actual frame entry. Only
non-system caller admission remains to be supplied. -/
theorem inhibited_mid_admitted {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (callers : trace.FrameAdmitted withdrawalRequestPredeployAddress
      (fun sevm _ => sevm.caller ≠ systemAddress)) :
    trace.FrameAdmitted withdrawalRequestPredeployAddress inhibitedEntry := by
  apply (trace.frameAdmitted_iff_rawFrames _ _).2
  intro root member target
  exact ⟨trace.rawFrames_entered enteredCondition_fresh root member,
    (trace.frameAdmitted_iff_rawFrames _ _).1 callers root member target⟩

/-- The remainder of the deployment block and all following selected-domain blocks
preserve the canonical code and represented initial storage. Caller exclusion is an
explicit intermediate admission premise; it is not inferred from deployment. -/
theorem inhibited_mid_history_preservesIn {F : Fork → Prop}
    (neutral : ∀ {f : Fork}, F f → NeutralFork f)
    (capabilities : BodyStageCapabilities F)
    {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future)
    (callers : trace.FrameAdmitted withdrawalRequestPredeployAddress
      (fun sevm _ => sevm.caller ≠ systemAddress))
    (installed : start.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (initialStorage : RepresentsStorage
      (start.state.getStor withdrawalRequestPredeployAddress).get initial) :
    future.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
    RepresentsStorage (future.state.getStor withdrawalRequestPredeployAddress).get initial := by
  have startInv : inhibitedSpec.StateInv withdrawalRequestPredeployAddress start.state :=
    ⟨by rw [installed]; rfl, trivial, initialStorage⟩
  have finishInv := trace.stateInv_admitted_semIn (inhibitedSpec_preservesIn neutral)
    capabilities (inhibited_mid_admitted trace callers) (trace.rewardCreditsFunded capabilities)
    startInv inhibitedInstalledCert rfl
  refine ⟨?_, finishInv.inv⟩
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj finishInv.code

end Blanc.Lift.WithdrawalRequest
