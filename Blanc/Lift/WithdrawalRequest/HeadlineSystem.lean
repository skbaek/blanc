import Blanc.Lift.WithdrawalRequest.HeadlineFee
import Blanc.Lift.WithdrawalRequest.NatLiveness
import Blanc.Lift.WithdrawalRequest.SystemHistory
import Blanc.Lift.WithdrawalRequest.DeploymentHistory

/-!
# EIP-7002 system call and submission liveness, rooted in the deployment

The system-call headline is per environment: canonical code installed and a covered fork
suffice. The history forms start from an actual deployment (`DeploymentHistory` and its
environmental `Admission`), which supply the installed code at the checkpoint, followed by
any configured history.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace

/-- The checked EIP-7002 system call returns without error and uses at most 210,000 gas. -/
def SystemCallOk (benv : Benv) : Prop :=
  ∃ post out, processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
      .ok (post, out) ∧
    systemTransactionGas - out.gasLeft ≤ 210000

/-- **EIP-7002 system call.** With canonical code installed, whatever storage holds, the
checked system call succeeds and uses at most 210,000 gas. -/
theorem system_call_succeeds {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    SystemCallOk benv := by
  obtain ⟨run, gasLeft, bound⟩ := checked_system_totality fork installed
  refine ⟨_, _, run, ?_⟩
  rw [gasLeft]
  omega

/-- **EIP-7002 system call after the deployment.** After the actual deployment, its admitted
preactivation prefix and any configured history, the checked system call on an environment
carrying the final state succeeds and uses at most 210,000 gas. -/
theorem history_system_call_succeeds {cfg : ChainConfig} {checkpoint future : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    {benv : Benv} (state : benv.state = future.state) (fork : CoveredFork benv.stat.fork) :
    SystemCallOk benv := by
  have installed : benv.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    rw [state]
    exact history_canonical_code history (deployment.initialized admission).checkpointCode
  exact system_call_succeeds fork installed

/-- Gas a fresh 56-byte submission is charged beyond the `G` it is left with, for a word fee
loop of `iterations` iterations: fixed and per-iteration execution, the schedule-dependent
storage reads, and the storage writes. -/
def submissionCost (fresh : Sevm) (base : Devm) (iterations : Nat) : Nat :=
  1258 + 87 * iterations + sloadScheduleCost fresh (userSubmissionReads fresh base) +
    submissionStoreGas fresh (afterSload fresh base 0) Mem.empty

/-- A fresh 56-byte user submission `data` to EIP-7002 at world state `world`: if the stored
excess is the inhibitor it cannot succeed; otherwise, paying at least the EIP fee, the word
fee loop has a unique result and the call succeeds from `G + submissionCost` gas, leaving
exactly `G`, for every `G` above the call stipend. -/
def SubmissionLive (world : Jaune.State) (sevm : Sevm) (b : Devm) (data : Bytes) : Prop :=
  let fresh := historySubmissionSevm world sevm data
  let base := b.withState world
  (storedExcess world = B256.max →
    ∀ gas post, ¬ Nonempty (Exec 0 fresh (St base [] Mem.empty gas) (.ok post))) ∧
  (storedExcess world ≠ B256.max → SpecFee (storedExcess world) ≤ sevm.value.toNat →
    ∃! result : Nat × B256,
      WordFakeExponential.Run (storedExcess world) 17 1 17 0 result.1 result.2 ∧
      ∀ G, gCallStipend < G →
        Nonempty (Exec 0 fresh (St base [] Mem.empty (G + submissionCost fresh base result.1))
          (.ok (submissionPost fresh (afterSload fresh base 0) Mem.empty G))))

/-- **EIP-7002 submission liveness after the deployment.** After the actual deployment, its
admitted preactivation prefix and any configured history, a 56-byte user submission paying the
EIP fee succeeds, leaving exactly `G` of `G + submissionCost` gas, unless the stored excess is
the inhibitor, in which case it cannot succeed. -/
theorem history_submission_live {cfg : ChainConfig} {checkpoint future : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    SubmissionLive future.state sevm b data :=
  history_submission_nat_live history (deployment.initialized admission).checkpointCode
    sevm b data fork user length

end Blanc.Lift.WithdrawalRequest
