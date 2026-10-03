import Blanc.Lift.WithdrawalRequest.FrameEffects
import Blanc.Lift.WithdrawalRequest.CodeFacts
import Blanc.StorageOnlySpec
import Blanc.ContractAdmissionSem
import Blanc.ExecutionTraceFresh
import Blanc.ExecutionTraceCalldata

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- Entry conditions obtained from retained frame initialization and header gas bounds. -/
def balanceEntryCondition (sevm : Sevm) (pre : Devm) : Prop :=
  Exec.FreshEntry sevm pre ∧ sevm.data.length < 2 ^ 256

theorem code_eq_of_image {c : ByteArray}
    (image : some c.toList = some Blanc.withdrawalRequestCode.toList) :
    c = Blanc.withdrawalRequestCode := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj image

/-- The canonical runtime's raw effect relation, conditional only on actual fresh entry. -/
def balanceSem : CodeSem where
  image := some Blanc.withdrawalRequestCode.toList
  Run sevm pre post := sevm.code = Blanc.withdrawalRequestCode ∧
    (CoveredFork sevm.benvStat.fork → balanceEntryCondition sevm pre →
      FrameEffect sevm pre post)
  correct := by
    intro sevm pre post run image
    have code := code_eq_of_image image
    refine ⟨code, fun fork entry => ?_⟩
    exact exec_frame_effect code fork entry.1.1
      (by rw [entry.1.2]; rfl) (by rw [entry.1.2]; exact Mem.wf_empty) entry.2 run
  ne_nil := by
    intro bytes image
    have eq := Option.some.inj image
    rw [← eq]
    exact withdrawalRequestCode_sem_facts.2
  not_delegation := by
    intro c image
    rw [code_eq_of_image image]
    exact withdrawalRequestCode_sem_facts.1

/-- E9 needs no queue invariant or fee arithmetic domain. -/
def balanceSpec : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly balanceSem (fun _ => True)

theorem balanceSpec_preserves : balanceSpec.PreservesAdmitted withdrawalRequestPredeployAddress
    balanceEntryCondition := by
  intro sevm pre post fork run admitted code wf inv
  exact ⟨trivial, trivial⟩

theorem history_balanceEntryCondition {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future) :
    trace.FrameAdmitted withdrawalRequestPredeployAddress balanceEntryCondition :=
  ExecutionTrace.ConfiguredHistoryTrace.FrameAdmitted.and
    (trace.freshFrameAdmitted withdrawalRequestPredeployAddress) trace.frameAdmitted_calldata

end Blanc.Lift.WithdrawalRequest
