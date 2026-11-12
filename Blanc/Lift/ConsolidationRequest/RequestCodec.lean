import Blanc.ConsensusSszConsolidation
import Blanc.JointFeed
import Blanc.Lift.ConsolidationRequest.Queue
import Blanc.Lift.RequestQueue.Link

/-!
# Consensus requests and the EIP-7251 queue record

A consensus request is the existing caller/calldata record. Reading type-2
SSZ bytes into 116-byte pieces recovers those records in their original order.
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune JauneConsensus Blanc.ConsensusSsz

/-- The caller and two public keys recorded by the consolidation contract. -/
def consensusRecord (cr : JauneConsensus.ConsolidationRequest) : Record where
  source := cr.source_address
  data := cr.source_pubkey.toArray.toList ++ cr.target_pubkey.toArray.toList
  data_length := by
    simp only [List.length_append, Array.length_toList,
      cr.source_pubkey.size_eq, cr.target_pubkey.size_eq]

/-- The actual consensus SSZ bytes are this contract record's returned bytes. -/
theorem out_consensusRecord (cr : JauneConsensus.ConsolidationRequest) :
    (consensusRecord cr).out = Ssz.serialize cr := by
  rw [serialize_consolidationRequest]
  rfl

/-- Type-2 request bytes, split using the shared fixed-width chunks. -/
def consensusRecords (requests : ExecutionRequestsList) : List Bytes :=
  RequestQueue.Link.chunks 116
    ((requests.filterMap (RequestQueue.Link.entryOf 2)).flatten)

/-- The engine's type-2 output recovers exactly the contract records, including empty lists. -/
theorem consensusRecords_getExecutionRequestsList {P : Preset} (r : ExecutionRequests P) :
    consensusRecords (getExecutionRequestsList r) =
      r.consolidations.toArray.toList.map (fun cr => (consensusRecord cr).out) := by
  have key : RequestQueue.Link.chunks 116 (Ssz.serialize r.consolidations) =
      r.consolidations.toArray.toList.map (fun cr => (consensusRecord cr).out) := by
    simp only [out_consensusRecord]
    rw [serialize_sszList_of_fixedSize (k := 116) rfl]
    exact RequestQueue.Link.chunks_flatMap 116 Ssz.serialize
      serialize_consolidationRequest_length (by decide) _
  have h02 : ¬ (0 : UInt8) = 2 := by decide
  have h12 : ¬ (1 : UInt8) = 2 := by decide
  rw [← key]
  unfold consensusRecords getExecutionRequestsList
  by_cases hd : (Ssz.serialize r.deposits).isEmpty <;>
  by_cases hw : (Ssz.serialize r.withdrawals).isEmpty <;>
  by_cases hc : (Ssz.serialize r.consolidations).isEmpty <;>
    simp_all only [List.isEmpty_iff, RequestQueue.Link.entryOf,
      JauneConsensus.depositRequestType, JauneConsensus.withdrawalRequestType,
      JauneConsensus.consolidationRequestType,
      List.filterMap_cons, List.filterMap_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, ↓reduceIte]

/-- A joint step's actual execution output carries those same ordered contract records. -/
theorem JointRunStep.consensusRecords_eq {P : Preset} {cfg : ChainConfig}
    {ccfg : Config} {bls : Bool} (D : Blanc.JointRunStep (P := P) cfg ccfg bls)
    {requests : ExecutionRequests P}
    (read : Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests) :
    consensusRecords D.keptBlock.output.requests =
      requests.consolidations.toArray.toList.map (fun cr => (consensusRecord cr).out) := by
  obtain ⟨r, hr, output⟩ := D.exists_executionRequests
  rw [read] at hr
  cases hr
  rw [output, consensusRecords_getExecutionRequestsList]

end Blanc.Lift.ConsolidationRequest
