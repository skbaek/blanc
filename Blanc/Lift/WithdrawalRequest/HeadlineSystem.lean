import Blanc.Lift.WithdrawalRequest.HeadlineFee
import Blanc.Lift.WithdrawalRequest.NatLiveness
import Blanc.Lift.WithdrawalRequest.SystemHistory
import Blanc.Lift.WithdrawalRequest.DeploymentHistory
import Blanc.Lift.WithdrawalRequest.MainnetDeployment

/-!
# EIP-7002 system call and submission liveness, rooted in the deployment

The system-call headline is per environment: canonical code installed and a covered fork
suffice. The history forms start from an actual deployment (`DeploymentHistory` and its
environmental `Admission`), which supply the installed code at the checkpoint, followed by
any configured history. A sibling headline states the queue effect of a successful
submission over the stored queue words. Each history form has an instance at the actual
mainnet deployment (`WithdrawalDeploymentObservation`).
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

/-- A successful fresh 56-byte user submission `data` to EIP-7002 at world state `world` appends
exactly one record to the stored queue: the caller's 20 bytes, the 48 public-key bytes and the
amount's 8 bytes in little-endian order (the withdrawal-output format of `submissionRecord`). -/
def SubmissionQueued (world : Jaune.State) (sevm : Sevm) (b : Devm) (data : Bytes) : Prop :=
  let fresh := historySubmissionSevm world sevm data
  ∀ gas post, Nonempty (Exec 0 fresh (St (b.withState world) [] Mem.empty gas) (.ok post)) →
    storedQueue (post.getStor withdrawalRequestPredeployAddress).get =
      storedQueue (world.getStor withdrawalRequestPredeployAddress).get ++
        [sevm.caller.toBytes ++ data.take 48 ++ (data.drop 48).reverse]

/-- **EIP-7002 submission queue effect after the deployment.** After the actual deployment, its
admitted preactivation prefix and any configured history with at most `wordOccurrenceCap`
committed submissions, every successful 56-byte user submission appends exactly its own record
to the stored queue. -/
theorem history_submission_queued {cfg : ChainConfig} {checkpoint future : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    SubmissionQueued future.state sevm b data := by
  intro gas post ⟨run⟩
  have init := deployment.initialized admission
  have installed : (historySubmissionSevm future.state sevm data).code =
      Blanc.withdrawalRequestCode := history_canonical_code history init.checkpointCode
  have cap : (history.settledFrames.flatMap submissionFramePayments).length ≤
      wordOccurrenceCap := by
    simpa only [submissions, List.length_map] using occurrences
  obtain ⟨events, _, _, _, rep, prefixes⟩ :=
    history_word_model history init.checkpointCode init.checkpointStorage cap
  obtain ⟨_, _, _, _, countLe, _, _, _, _, slotLt, _⟩ := prefixes events [] (List.append_nil _).symm
  have bounds : SubmissionBounds (events.foldl wordModelUpdate Blanc.WithdrawalRequest.initial) :=
    ⟨Nat.lt_of_le_of_lt (Nat.add_le_add_right countLe 1) (by decide), slotLt⟩
  have lengthBound : (historySubmissionSevm future.state sevm data).data.length < 2 ^ 256 := by
    change data.length < 2 ^ 256
    rw [length]
    decide
  have effect := exec_frame_effect (pre := St (b.withState future.state) [] Mem.empty gas)
    installed fork rfl rfl Mem.wf_empty lengthBound run
  cases effect with
  | system caller _ _ _ => exact absurd caller user
  | getter _ empty _ _ _ _ _ _ _ _ =>
    change data = [] at empty
    rw [empty] at length
    exact absurd length (by decide)
  | submission _ _ hlen _ _ _ _ _ g state =>
    subst state
    have baseRep : Blanc.WithdrawalRequest.RepresentsStorage
        ((afterSload (historySubmissionSevm future.state sevm data)
          (St (b.withState future.state) [] Mem.empty gas) 0).getStor
          (historySubmissionSevm future.state sevm data).currentTarget).get
        (events.foldl wordModelUpdate Blanc.WithdrawalRequest.initial) := by
      rw [afterSload_getStor]
      exact rep
    have postRep := submissionPost_represents _ _
      (St (b.withState future.state) [] Mem.empty gas).memory g _ _ baseRep bounds rfl
      (decodeSubmission_payload _ hlen).symm
    change Blanc.WithdrawalRequest.RepresentsStorage
      (Devm.getStor _ withdrawalRequestPredeployAddress).get _ at postRep
    rw [storedQueue_eq postRep, storedQueue_eq rep]
    simp only [Blanc.WithdrawalRequest.submit, List.map_append, List.map_cons, List.map_nil,
      Blanc.WithdrawalRequest.outputRecord, decodeSubmission, Blanc.Bytes.toBytes_toUInt64_of_length
        (show ((historySubmissionSevm future.state sevm data).data.drop 48).length = 8 by
          rw [List.length_drop, hlen])]
    rfl

/-! ## Mainnet instances -/

/-- **EIP-7002 system call from the actual mainnet deployment.** For the observed deployment
block (its position-0 cut), the following Cancun blocks to the last pre-Prague checkpoint and any
configured history after it, the checked system call on an environment carrying the final state
succeeds and uses at most 210,000 gas. -/
theorem history_system_call_succeeds_mainnet {before after checkpoint future : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint future)
    {benv : Benv} (state : benv.state = future.state) (fork : CoveredFork benv.stat.fork) :
    SystemCallOk benv :=
  history_system_call_succeeds (mainnetDeploymentHistory block cut following obs)
    (mainnetDeploymentHistory_admission block cut following obs prefixSystemAvoid)
    history state fork

/-- **EIP-7002 submission liveness from the actual mainnet deployment**, over the same observed
deployment, prefix and checkpoint as `history_system_call_succeeds_mainnet`. -/
theorem history_submission_live_mainnet {before after checkpoint future : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint future)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    SubmissionLive future.state sevm b data :=
  history_submission_live (mainnetDeploymentHistory block cut following obs)
    (mainnetDeploymentHistory_admission block cut following obs prefixSystemAvoid)
    history sevm b data fork user length

/-- **EIP-7002 submission queue effect from the actual mainnet deployment**, over the same
observed deployment, prefix and checkpoint as `history_system_call_succeeds_mainnet`, with the
same cumulative submission cap as `history_fifo_mainnet`. -/
theorem history_submission_queued_mainnet {before after checkpoint future : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint future)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    SubmissionQueued future.state sevm b data :=
  history_submission_queued (mainnetDeploymentHistory block cut following obs)
    (mainnetDeploymentHistory_admission block cut following obs prefixSystemAvoid)
    history occurrences sevm b data fork user length

end Blanc.Lift.WithdrawalRequest
