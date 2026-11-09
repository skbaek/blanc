import Blanc.ConsensusSsz
import Blanc.JointHistory
import Blanc.Lift.WithdrawalRequest.HistoryFifo

/-!
# The EIP-7002 record and the consensus `WithdrawalRequest`

The SSZ serialization of a consensus `WithdrawalRequest` is the contract's 76-byte system
return record (`outputRecord`): the 20-byte source address, the 48-byte public key, and the
amount's 8 little-endian bytes. It is injective. Reading type-1 records from
`get_execution_requests_list` returns exactly the serializations of the body's withdrawal
requests, in order.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus Blanc.ConsensusSsz Blanc.WithdrawalRequest

/-- The EIP-7002 contract entry a consensus withdrawal request stands for. -/
def consensusEntry (wr : JauneConsensus.WithdrawalRequest) : Blanc.WithdrawalRequest.Entry where
  caller := wr.source_address
  pubkey := ⟨wr.validator_pubkey.toArray.toList, by
    simp only [Array.length_toList, wr.validator_pubkey.size_eq]⟩
  amount := wr.amount.toWord

/-- A withdrawal request's SSZ serialization is the contract's system return record of its
entry; the record's amount bytes are the little-endian ones. -/
theorem outputRecord_consensusEntry (wr : JauneConsensus.WithdrawalRequest) :
    outputRecord (consensusEntry wr) = Ssz.serialize wr := by
  rw [serialize_withdrawalRequest, outputRecord, consensusEntry]
  simp only [List.append_assoc]
  rw [show wr.amount.toNat = wr.amount.toWord.toNat from rfl, leBytes_eight_eq_reverse_toBytes]

/-- A whole 76-byte record in front is split off as the first record. -/
theorem withdrawalRecords_append_of_length {r rest : Bytes} (hr : r.length = 76) :
    withdrawalRecords (r ++ rest) = r :: withdrawalRecords rest := by
  unfold withdrawalRecords
  rw [List.length_append, hr,
    show (76 + rest.length + 75) / 76 = (rest.length + 75) / 76 + 1 by omega,
    List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1
  · simp only [← hr, mul_zero, List.drop_zero, List.take_left']
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one]
    rw [show 76 * i + 76 = r.length + 76 * i by omega, List.drop_append,
      List.drop_eq_nil_of_le (by omega), Nat.add_sub_cancel_left, List.nil_append]

/-- Whole 76-byte records concatenated split back into themselves. -/
theorem withdrawalRecords_flatten {rs : List Bytes} (h : ∀ r ∈ rs, r.length = 76) :
    withdrawalRecords rs.flatten = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatten_cons, withdrawalRecords_append_of_length (h r (by simp only [List.mem_cons, true_or])),
      ih fun r' hr' => h r' (by simp only [List.mem_cons, hr', or_true])]

/-- The type-1 records of `get_execution_requests_list` are the serializations of the body's
withdrawal requests, in order. An empty withdrawal list contributes no entry and no record. -/
theorem withdrawalRequestRecords_getExecutionRequestsList {P : Preset}
    (r : ExecutionRequests P) :
    withdrawalRequestRecords (getExecutionRequestsList r) =
      r.withdrawals.toArray.toList.map Ssz.serialize := by
  have key : withdrawalRecords (Ssz.serialize r.withdrawals) =
      r.withdrawals.toArray.toList.map Ssz.serialize := by
    rw [serialize_sszList_of_fixedSize (k := 76) rfl]
    exact withdrawalRecords_flatten fun b hb => by
      obtain ⟨wr, -, rfl⟩ := List.mem_map.mp hb
      exact serialize_withdrawalRequest_length wr
  rw [← key]
  have hnil : withdrawalRecords [] = [] := rfl
  have h01 : ¬((0 : UInt8) = 1) := by decide
  have h21 : ¬((2 : UInt8) = 1) := by decide
  unfold getExecutionRequestsList
  by_cases hd : (Ssz.serialize r.deposits).isEmpty <;>
  by_cases hw : (Ssz.serialize r.withdrawals).isEmpty <;>
  by_cases hc : (Ssz.serialize r.consolidations).isEmpty <;>
    simp_all only [List.isEmpty_iff, withdrawalRequestRecords, ↓reduceIte,
      List.filterMap_cons_none, JauneConsensus.withdrawalRequestType,
      JauneConsensus.consolidationRequestType, JauneConsensus.depositRequestType,
      List.filterMap_nil, List.flatMap_nil, Option.some.injEq, List.filterMap_cons_some,
      List.flatMap_cons, List.append_nil, List.nil_append]

/-- A joint step's execution block emits, as type-1 records, exactly the serializations of the
beacon block's withdrawal requests, in order. -/
theorem JointStepTrace.withdrawalRequestRecords_eq {P : Preset} {cfg : ChainConfig}
    {ccfg : Config} {bls : Bool} {s s' : JointState P} {b : AnySignedBlock P}
    (t : JointStepTrace cfg ccfg bls s s' b) :
    ∃ requests : ExecutionRequests P,
      Gated.read b.2.message.body.execution_requests "NewPayloadRequest: execution_requests" =
        .ok requests ∧
      withdrawalRequestRecords t.trace.blockOutput.requests =
        requests.withdrawals.toArray.toList.map Ssz.serialize := by
  obtain ⟨requests, hread, hreq⟩ := ofBlock_executionRequests t.ofBlock
  refine ⟨requests, hread, ?_⟩
  rw [t.requests_eq, hreq, withdrawalRequestRecords_getExecutionRequestsList]

end Blanc.Lift.WithdrawalRequest
