import Blanc.Lift.WithdrawalRequest.WordFifo
import Blanc.Lift.WithdrawalRequest.ProtocolOccurrences
import Blanc.Lift.WithdrawalRequest.HistoryFifo

/-!
# E5(ii): what a mid-block drain does to the FIFO conclusion

`history_fifo_of_checkpoint` assumes no code at SYSTEM_ADDRESS. A frame whose caller is
SYSTEM_ADDRESS (see `SystemDrain.drain_exec`) can dequeue a committed submission before the
block's own system call, so that it is never emitted. `HistoryFifoCheckpointLoadBearing` states
that such a history exists; `block_submissions_eq_transactions` and `system_submissions_eq_nil`
locate a block's submission payments in its transactions.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

/-- A system message whose target holds spawn-free, non-delegating code other than the
withdrawal predeploy's settles no submission payment: every settled frame targets it. -/
theorem system_submissions_eq_nil
    {benv : Benv} {target : Adr} {data : Bytes} {state : Jaune.State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (code : ByteArray)
    (installed : benv.state.getCode target = code)
    (reach : SpawnFreeReach code) (nondelegating : ¬ isValidDelegation code)
    (foreign : target ≠ withdrawalRequestPredeployAddress) :
    trace.settledFrames.flatMap submissionFramePayments = [] := by
  have confined := trace.rawFrames_target_of_code
    (installed ▸ reach) (installed ▸ nondelegating)
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  have targetEq := confined (Blanc.Exec.Frame.rootDeriv (frame := frame))
    (trace.mem_rawFrames_of_mem_settledFrames frame member)
  unfold submissionFramePayments
  exact ite_eq_right (fun submission => foreign (targetEq.symm.trans submission.1.1))

/-- **A block's submission payments are its transactions'.**  With the canonical system code
installed at the checkpoint, the beacon-roots, history-storage and consolidation messages
settle no frame at the predeploy, and the withdrawal message's only frame has caller
SYSTEM_ADDRESS.  No SYSTEM_ADDRESS exclusion is needed. -/
theorem block_submissions_eq_transactions {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state) :
    block.settledFrames.flatMap submissionFramePayments =
      block.bodyTrace.transactions.settledFrames.flatMap submissionFramePayments := by
  have beaconMember : (beaconRootsAddress, beaconRootsCode) ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl trivial
  have historyMember : (historyStorageAddress, historyStorageCode) ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inl trivial)
  have withdrawalMember : (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
      ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
  have consolidationMember : (consolidationRequestPredeployAddress, consolidationRequestCode)
      ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr trivial))
  have beaconFacts := systemContracts_facts _ beaconMember
  have historyFacts := systemContracts_facts _ historyMember
  have consolidationFacts := systemContracts_facts _ consolidationMember
  have beaconCode := history.block_code_boundaries block beaconRootsAddress beaconRootsCode
    beaconFacts.2.2 beaconFacts.2.1 (installed _ beaconMember)
  have historyCode := history.block_code_boundaries block historyStorageAddress historyStorageCode
    historyFacts.2.2 historyFacts.2.1 (installed _ historyMember)
  have consolidationCode := history.block_code_boundaries block
    consolidationRequestPredeployAddress consolidationRequestCode
    consolidationFacts.2.2 consolidationFacts.2.1 (installed _ consolidationMember)
  have beaconEmpty := system_submissions_eq_nil block.bodyTrace.beacon beaconRootsCode
    beaconCode.1 beaconFacts.1 beaconFacts.2.1 (by decide +kernel)
  have historyEmpty := system_submissions_eq_nil block.bodyTrace.history historyStorageCode
    historyCode.2.1 historyFacts.1 historyFacts.2.1 (by decide +kernel)
  have consolidationEmpty := system_submissions_eq_nil block.bodyTrace.requests.consolidation
    consolidationRequestCode consolidationCode.2.2.2 consolidationFacts.1
    consolidationFacts.2.1 (by decide +kernel)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, resetEmpty, _⟩ :=
    block_requests_reset_occurrence history block (installed _ withdrawalMember)
  simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
    RequestsTrace.settledFrames, List.flatMap_append, beaconEmpty, historyEmpty,
    consolidationEmpty, resetEmpty, List.nil_append, List.append_nil]

/-- **The negative control at the public FIFO law, as a proposition.** A configured history
meeting every premise of `history_fifo_of_checkpoint` except `systemEmpty` (code at
SYSTEM_ADDRESS instead) for which `HistoryFifo` itself fails.

Scope: this negates the checkpoint form `history_fifo_of_checkpoint`, not the deployment-rooted
headline `history_fifo`, whose premises contain no `systemEmpty`: there SYSTEM emptiness is
derived from `DeploymentHistory.Admission`. The control shows that this derivation is
load-bearing, not that a premise of `history_fifo` is. -/
def HistoryFifoCheckpointLoadBearing : Prop :=
  ∃ (cfg : ChainConfig) (checkpoint final : BlockChain)
    (history : ConfiguredHistoryTrace cfg checkpoint final),
    SystemCodeInstalled checkpoint.state ∧
    history.NoSenderAt systemAddress ∧
    history.NoAuthorityAt systemAddress ∧
    (∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress) ∧
    checkpoint.state.getCode systemAddress ≠ ByteArray.empty ∧
    RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial ∧
    (submissions history).length ≤ wordOccurrenceCap ∧
    ¬ HistoryFifo history

end Blanc.Lift.WithdrawalRequest
