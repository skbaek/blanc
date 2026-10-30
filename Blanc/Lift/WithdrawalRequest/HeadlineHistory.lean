import Blanc.Lift.WithdrawalRequest.MainnetDeployment
import Blanc.Lift.WithdrawalRequest.Creation.Deploy

/-!
# EIP-7002 deployment, payment and delivery headlines over direct observers

Each headline below concludes one named proposition built from observers that read the
execution directly: the four bookkeeping storage words, the balance word and the values of
committed submission frames, the stored queue at a block's request boundary, and the
withdrawal records of a block's actual request list. No queue model, representation
relation or existential witness occurs in a conclusion; the model correspondence is proved
below each observer. Every history form is rooted in a `DeploymentHistory`, and each has an
instance at the actual mainnet deployment (`WithdrawalDeploymentObservation`).
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.ExecutionTrace Blanc.WithdrawalRequest ExecutionAccountingReplay

/-! ## Deployment -/

/-- The four EIP-7002 bookkeeping words read as numbers: the excess word (slot 0) holds
`2^256 - 1`, the inhibitor, and the count, head and tail words (slots 1-3) are zero. -/
def InitialWords (storage : B256 → B256) : Prop :=
  (storage 0).toNat = 2 ^ 256 - 1 ∧ (storage 1).toNat = 0 ∧ (storage 2).toNat = 0 ∧
    (storage 3).toNat = 0

/-- Storage representing INIT holds the initial words. -/
theorem initialWords_of_represents {storage : B256 → B256}
    (rep : RepresentsStorage storage initial) : InitialWords storage := by
  have zero : (0 : Nat) < 2 ^ 256 := Nat.two_pow_pos 256
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rep.excess]
    exact B256.toNat_toB256_of_lt (Nat.sub_lt zero Nat.one_pos)
  · rw [rep.count]
    exact B256.toNat_toB256_of_lt zero
  · rw [rep.head]
    exact B256.toNat_toB256_of_lt zero
  · rw [rep.tail]
    exact B256.toNat_toB256_of_lt zero

/-- **EIP-7002 deployment.** For a deployment at an actual transaction position followed by
its admitted preactivation (all-Cancun) history, the committed state right after the
deployment transaction and the checkpoint state both carry the canonical runtime at the
predeploy and the initial words: the inhibitor excess and zero count, head and tail. -/
theorem deploy {cfg : ChainConfig} {checkpoint : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission) :
    deployment.deployment.cut.afterBenv.state.getCode withdrawalRequestPredeployAddress =
        Blanc.withdrawalRequestCode ∧
      InitialWords
        (deployment.deployment.cut.afterBenv.state.getStor withdrawalRequestPredeployAddress).get ∧
      checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      InitialWords (checkpoint.state.getStor withdrawalRequestPredeployAddress).get := by
  have initialized := deployment.initialized admission
  exact ⟨initialized.deployedCode, initialWords_of_represents initialized.deployedStorage,
    initialized.checkpointCode, initialWords_of_represents initialized.checkpointStorage⟩

/-! ## Payments -/

/-- The total value of all committed EIP-7002 submissions in the history (the frames
selected by `submissionFramePayments`: nonstatic, non-SYSTEM calls with 56 bytes of input). -/
def submissionPaid {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) : Nat :=
  ((history.settledFrames.flatMap submissionFramePayments).map Prod.snd).sum

private theorem submissionCreditPayments_sum_le (steps : List SignedBalanceCredit) :
    ((steps.flatMap submissionCreditPayments).map Prod.snd).sum ≤
      (steps.map SignedBalanceCredit.amount).sum := by
  have single (credit : SignedBalanceCredit) :
      ((submissionCreditPayments credit).map Prod.snd).sum ≤ credit.amount := by
    cases credit with
    | message frame =>
      by_cases paid : submissionPaymentFrame frame
      · simp only [submissionCreditPayments, ite_eq_left paid, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, Nat.le_refl]
      · simp only [submissionCreditPayments, ite_eq_right paid, List.map_nil, List.sum_nil,
          Nat.zero_le]
    | incidental amount => exact Nat.zero_le _
  induction steps with
  | nil => exact Nat.le_refl 0
  | cons credit rest ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    have := single credit
    omega

/-- Supporting form of `history_payments` from canonical code at the checkpoint. -/
theorem history_payments_of_checkpoint {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat + submissionPaid history ≤
      (final.state.bal withdrawalRequestPredeployAddress).toNat := by
  obtain ⟨steps, balance, payments⟩ := history_submission_payments history code
  have bound := submissionCreditPayments_sum_le steps
  rw [payments] at bound
  unfold submissionPaid
  omega

/-- **EIP-7002 payments.** After a deployment and its admitted preactivation history, in any
subsequent configured history the predeploy's final balance is at least its checkpoint
balance plus the value of every committed submission. -/
theorem history_payments {cfg : ChainConfig} {checkpoint final : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint final) :
    (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat + submissionPaid history ≤
      (final.state.bal withdrawalRequestPredeployAddress).toNat :=
  history_payments_of_checkpoint history (deployment.initialized admission).checkpointCode

/-! ## Delivery -/

/-- The stored queue (head to tail, in withdrawal-output format) at a block's request
boundary, the state the block's withdrawal system call reads. -/
def queueAtRequests {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTrace cfg pre post) : List Bytes :=
  storedQueue (block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress).get

/-- The withdrawal records of a block's actual request list. -/
def blockWithdrawals {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTrace cfg pre post) : List Bytes :=
  withdrawalRequestRecords block.blockOutput.requests

/-- The record at position `q` of block B's stored queue is published by block D as its
record `q % 16`, preceded in order by exactly the queue entries ahead of it from position
`16 * (q / 16)`. -/
def Delivered {cfg : ChainConfig} {preB postB preD postD : BlockChain}
    (blockB : ConfiguredBlockTrace cfg preB postB) (blockD : ConfiguredBlockTrace cfg preD postD)
    (q : Nat) : Prop :=
  ∀ record, (queueAtRequests blockB)[q]? = some record →
    (blockWithdrawals blockD)[q % 16]? = some record ∧
    (blockWithdrawals blockD).take (q % 16 + 1) =
      ((queueAtRequests blockB).drop (16 * (q / 16))).take (q % 16 + 1)

/-- A block's published withdrawal records are the records of the model represented at its
request boundary. This is the block-output form of `emission_eq_records`; the transaction
prefix of the request list is empty. -/
theorem blockWithdrawals_eq_of_request_rep {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (model : Blanc.WithdrawalRequest.State)
    (rep : RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get model) :
    blockWithdrawals block = (emitted model).map outputRecord := by
  have payload := block_requests_of_request_rep history block code model rep
  rw [blockWithdrawals, payload.2.1, block.bodyTrace.transaction_requests_eq_nil, List.nil_append]
  simp only [withdrawalRequestRecords, List.flatMap_append]
  change withdrawalRequestRecords (optionalRequestEntry 0 _) ++
    withdrawalRequestRecords (optionalRequestEntry 1 _) ++
    withdrawalRequestRecords (optionalRequestEntry 2 _) = _
  rw [withdrawalRequestRecords_optional, withdrawalRequestRecords_optional,
    withdrawalRequestRecords_optional, ite_eq_right (by decide), ite_eq_left rfl,
    ite_eq_right (by decide),
    List.nil_append, List.append_nil, systemOutput, withdrawalRecords_outputRecords]

/-- **EIP-7002 delivery.** After a deployment and its admitted preactivation history, let the
history through block D extend the history through block B by exactly `q / 16` further
blocks. Then the record at position `q` of B's stored queue at its request boundary is
published by D as its withdrawal record `q % 16`, after exactly the stored entries ahead of
it. The other system installations, the SYSTEM exclusions and the cumulative submission cap
are the same explicit assumptions as `history_fifo`. -/
theorem history_delivery
    {cfg : ChainConfig} {checkpoint preB postB preD postD : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (historyB : ConfiguredHistoryTrace cfg checkpoint preB)
    (blockB : ConfiguredBlockTrace cfg preB postB)
    (historyD : ConfiguredHistoryTrace cfg checkpoint preD)
    (blockD : ConfiguredBlockTrace cfg preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions (ConfiguredHistoryTrace.step historyD blockD)).length ≤
      wordOccurrenceCap)
    {q : Nat} (exactDepth : depth = q / 16) :
    Delivered blockB blockD q := by
  have initialized := deployment.initialized admission
  have occurrencesD : ((ConfiguredHistoryTrace.step historyD blockD).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap := by
    simpa only [submissions, List.length_map] using occurrences
  have occurrencesB : ((ConfiguredHistoryTrace.step historyB blockB).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap := by
    obtain ⟨suffix, frames⟩ := extension.settledFrames
    rw [frames, List.flatMap_append, List.length_append] at occurrencesD
    omega
  obtain ⟨r, boundary, -⟩ := block_word_fifo_of_checkpoint historyB blockB
    (otherInstalled.with_withdrawal initialized.checkpointCode)
    (extension.noSenderAt senders) (extension.noAuthorityAt authorities)
    (fun root member => avoid root (extension.rawFrames_mem root member))
    initialized.systemEmpty initialized.checkpointStorage occurrencesB
  have queueB : queueAtRequests blockB = r.model.queue.map outputRecord :=
    storedQueue_eq boundary.represents
  intro record stored
  rw [queueB, List.getElem?_map, Option.map_eq_some_iff] at stored
  obtain ⟨entry, queued, rfl⟩ := stored
  obtain ⟨modelD, repD, -, position, ahead⟩ := block_word_delivery_from_deployment deployment
    admission historyB blockB historyD blockD extension otherInstalled senders authorities avoid
    occurrencesD r.model boundary.represents queued exactDepth
  rw [blockWithdrawals_eq_of_request_rep historyD blockD initialized.checkpointCode modelD repD,
    queueB, ← exactDepth]
  refine ⟨by rw [List.getElem?_map, position]; rfl, ?_⟩
  rw [← List.map_take, ahead, ← List.map_drop, ← List.map_take]

/-! ## Mainnet instances -/

/-- **EIP-7002 deployment at mainnet.** For the observed deployment block (its position-0
cut) and the following Cancun blocks to the last pre-Prague checkpoint, the state right after
the deployment transaction and the checkpoint state carry the canonical runtime and the
initial words. -/
theorem deploy_mainnet {before after checkpoint : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress) :
    cut.afterBenv.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      InitialWords (cut.afterBenv.state.getStor withdrawalRequestPredeployAddress).get ∧
      checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      InitialWords (checkpoint.state.getStor withdrawalRequestPredeployAddress).get :=
  deploy (mainnetDeploymentHistory block cut following obs)
    (mainnetDeploymentHistory_admission block cut following obs prefixSystemAvoid)

/-- **EIP-7002 payments from the actual mainnet deployment**, over the same observed
deployment, prefix and checkpoint as `history_fifo_mainnet`. -/
theorem history_payments_mainnet {before after checkpoint final : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint final) :
    (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat + submissionPaid history ≤
      (final.state.bal withdrawalRequestPredeployAddress).toNat :=
  history_payments (mainnetDeploymentHistory block cut following obs)
    (mainnetDeploymentHistory_admission block cut following obs prefixSystemAvoid)
    history

/-- **EIP-7002 delivery from the actual mainnet deployment**, over the same observed
deployment, prefix and checkpoint as `history_fifo_mainnet`. -/
theorem history_delivery_mainnet
    {before after checkpoint preB postB preD postD : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (historyB : ConfiguredHistoryTrace mainnetChainConfig checkpoint preB)
    (blockB : ConfiguredBlockTrace mainnetChainConfig preB postB)
    (historyD : ConfiguredHistoryTrace mainnetChainConfig checkpoint preD)
    (blockD : ConfiguredBlockTrace mainnetChainConfig preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions (ConfiguredHistoryTrace.step historyD blockD)).length ≤
      wordOccurrenceCap)
    {q : Nat} (exactDepth : depth = q / 16) :
    Delivered blockB blockD q :=
  history_delivery (mainnetDeploymentHistory block cut following obs)
    (mainnetDeploymentHistory_admission block cut following obs prefixSystemAvoid)
    historyB blockB historyD blockD extension ⟨obs.beaconAtP, obs.historyAtP, obs.consolidationAtP⟩
    senders authorities avoid occurrences exactDepth

end Blanc.Lift.WithdrawalRequest
