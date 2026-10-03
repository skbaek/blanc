import Blanc.ExecutionImmutableCode
import Blanc.ExecutionTraceSystemCode
import Blanc.Lift.WithdrawalRequest.ResetOccurrence
import Blanc.Lift.WithdrawalRequest.UserOccurrence

/-! The actual block's withdrawal-target observations retain transaction order
and end in the single canonical protocol reset. The other protocol subtrees
contribute no such observation. This establishes neither Nat payment nor FIFO. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace

private theorem system_observations_eq_nil
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (code : ByteArray)
    (installed : benv.state.getCode target = code)
    (reach : SpawnFreeReach code) (nondelegating : ¬ isValidDelegation code)
    (foreign : target ≠ withdrawalRequestPredeployAddress) :
    trace.settledFrames.flatMap balanceFrameObservation = [] := by
  have confined := trace.rawFrames_target_of_code
    (installed ▸ reach) (installed ▸ nondelegating)
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  have targetEq := confined (Blanc.Exec.Frame.rootDeriv (frame := frame))
    (trace.mem_rawFrames_of_mem_settledFrames frame member)
  exact balanceFrameObservation_foreign frame (fun target => foreign (targetEq.symm.trans target))

/-- Under canonical installed code and the SYSTEM environment exclusions, the
actual target observations are precisely the transaction prefix followed by
the canonical nonstatic SYSTEM reset at the retained withdrawal boundary. -/
theorem block_protocol_observation_partition
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (initial : checkpoint.state.getCode systemAddress = ByteArray.empty) :
    ∃ reset : Exec.Frame,
      block.settledFrames.flatMap balanceFrameObservation =
        block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ++ [reset] ∧
      reset.sevm.currentTarget = withdrawalRequestPredeployAddress ∧
      reset.sevm.caller = systemAddress ∧
      reset.sevm.isStatic = false ∧
      reset.pre.state = block.bodyTrace.requestBenv.state ∧
      reset.post.state = block.bodyTrace.requests.withdrawalState ∧
      (reset.post.getStor withdrawalRequestPredeployAddress).get 1 = 0 ∧
      (∀ frame ∈ block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation,
        frame.sevm.caller ≠ systemAddress) := by
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
  have beaconEmpty := system_observations_eq_nil block.bodyTrace.beacon beaconRootsCode
    beaconCode.1 beaconFacts.1 beaconFacts.2.1 (by decide +kernel)
  have historyEmpty := system_observations_eq_nil block.bodyTrace.history historyStorageCode
    historyCode.2.1 historyFacts.1 historyFacts.2.1 (by decide +kernel)
  have consolidationEmpty := system_observations_eq_nil block.bodyTrace.requests.consolidation
    consolidationRequestCode consolidationCode.2.2.2 consolidationFacts.1
    consolidationFacts.2.1 (by decide +kernel)
  obtain ⟨reset, _, target, caller, dynamic, entry, endpoint, _, count, resetObs, _⟩ :=
    block_requests_reset_occurrence history block (installed _ withdrawalMember)
  refine ⟨reset, ?_, target, caller, dynamic, entry, endpoint, count, ?_⟩
  · simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
      RequestsTrace.settledFrames, List.flatMap_append, beaconEmpty, historyEmpty,
      consolidationEmpty, resetObs, List.nil_append, List.append_nil]
  · intro frame member
    obtain ⟨source, sourceMember, observation⟩ := List.mem_flatMap.mp member
    have same : frame = source := by
      unfold balanceFrameObservation at observation
      split at observation
      · exact List.mem_singleton.mp observation
      · exact False.elim (List.not_mem_nil observation)
    rw [same]
    exact block_settled_transaction_caller_ne_system history block
      senders authorities avoid initial source sourceMember

end Blanc.Lift.WithdrawalRequest
