import Blanc.ConsensusSsz
import Blanc.Lift.BuilderRequest.Deposit.Indexed
import Blanc.Lift.BuilderRequest.Exit.Indexed
import JauneConsensus.GloasAccessors

/-!
# The EIP-8282 records and the Gloas builder requests

The SSZ serialization of a Gloas `BuilderDepositRequest` is 184 bytes (key, credentials, the amount's
8 little-endian bytes, signature), of a `BuilderExitRequest` 68 bytes (source address, key). Reading the
type-3 (type-4) records of a block whose output requests are `get_execution_requests_list` of a Gloas
`ExecutionRequests` returns exactly the serializations of its builder deposits (exits), in order: the
emission side of the joint seam (statements.md §0.7, the feed part of `history_block`).

`depositRecord_amount` (B2, F3) is the endianness chain of a deposit record: the record's amount is the 8
calldata bytes at offset 80, read big-endian (`Bytes.toNat`); the returned record carries them reversed,
which is the SSZ (little-endian) encoding of the same `uint64`. `depositRecord_amount_byte_order` is its
control: the little-endian bytes of `10^9` read big-endian are not `10^9`.
-/

namespace Blanc.Lift.BuilderRequest.RequestCodecG

open Jaune JauneConsensus Blanc.ConsensusSsz ChainLink

/-- A progressive list of fixed-size elements serializes to the concatenation of its elements. -/
theorem serialize_progressiveList_of_fixedSize {s : Spine} {α : Type} [Ssz α] {k : Nat}
    (hk : Ssz.fixedSize? α = some k) (l : ProgressiveListS s α) :
    Ssz.serialize l = l.toArray.toList.flatMap Ssz.serialize := by
  show serializeParts (seqParts l.toArray.toList) = _
  unfold seqParts
  rw [hk]
  exact serializeParts_fixed _ _

/-- The SSZ serialization of a builder deposit request, field by field. -/
theorem serialize_builderDepositRequest (r : Gloas.BuilderDepositRequest) :
    Ssz.serialize r =
      r.pubkey.toArray.toList ++ r.withdrawal_credentials.toBytes ++ leBytes 8 r.amount.toNat ++
        r.signature.toArray.toList := by
  change serializeParts [fieldPart r.pubkey, fieldPart r.withdrawal_credentials, fieldPart r.amount,
    fieldPart r.signature] = _
  simp only [fieldPart]
  rw [show Ssz.fixedSize? BLSPubkey = some 48 from rfl, show Ssz.fixedSize? Bytes32 = some 32 from rfl,
    show Ssz.fixedSize? U64 = some 8 from rfl, show Ssz.fixedSize? BLSSignature = some 96 from rfl]
  have := serializeParts_fixed (fun b : Bytes => b)
    [Ssz.serialize r.pubkey, Ssz.serialize r.withdrawal_credentials, Ssz.serialize r.amount,
      Ssz.serialize r.signature]
  simp only [List.map] at this
  rw [this, serialize_byteVector, serialize_byteVector]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-- A builder deposit request serializes to 184 bytes. -/
theorem serialize_builderDepositRequest_length (r : Gloas.BuilderDepositRequest) :
    (Ssz.serialize r).length = 184 := by
  rw [serialize_builderDepositRequest]
  simp only [List.length_append, length_leBytes, Array.length_toList, r.pubkey.size_eq,
    B256.length_toBytes, r.signature.size_eq]

/-- The SSZ serialization of a builder exit request, field by field. -/
theorem serialize_builderExitRequest (r : Gloas.BuilderExitRequest) :
    Ssz.serialize r = r.source_address.toBytes ++ r.pubkey.toArray.toList := by
  change serializeParts [fieldPart r.source_address, fieldPart r.pubkey] = _
  simp only [fieldPart]
  rw [show Ssz.fixedSize? Adr = some 20 from rfl, show Ssz.fixedSize? BLSPubkey = some 48 from rfl]
  have := serializeParts_fixed (fun b : Bytes => b) [Ssz.serialize r.source_address, Ssz.serialize r.pubkey]
  simp only [List.map] at this
  rw [this, serialize_byteVector]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

/-- A builder exit request serializes to 68 bytes. -/
theorem serialize_builderExitRequest_length (r : Gloas.BuilderExitRequest) :
    (Ssz.serialize r).length = 68 := by
  rw [serialize_builderExitRequest]
  simp only [List.length_append, Array.length_toList, r.pubkey.size_eq]
  rfl

/-- The bytes of type `ty` in a typed request list whose empty entries are dropped: the data of the entries of
that type, concatenated. -/
theorem entries_filterMap (ty : UInt8) : ∀ L : List (UInt8 × Bytes),
    ((L.filterMap fun (p : UInt8 × Bytes) => if p.2.isEmpty then none else some (p.1 :: p.2)).filterMap
        (entryOf ty)).flatten = (L.filter fun p => p.1 = ty).flatMap Prod.snd
  | [] => rfl
  | (t, d) :: L => by
    have ih := entries_filterMap ty L
    by_cases hd : d.isEmpty
    · have hd' : d = [] := List.isEmpty_iff.mp hd
      subst hd'
      by_cases ht : t = ty <;>
        simp only [List.filterMap_cons, List.isEmpty_nil, ↓reduceIte, List.filter_cons, ht,
          decide_true, decide_false, List.flatMap_cons, List.nil_append, ih, Bool.false_eq_true]
    · by_cases ht : t = ty <;>
        simp only [List.filterMap_cons, hd, ↓reduceIte, entryOf, ht, List.flatten_cons, List.filter_cons,
          decide_true, decide_false, List.flatMap_cons, ih, Bool.false_eq_true]

/-- The type-3 and type-4 entries of `get_execution_requests_list`: the serializations of the builder
deposit and builder exit lists (an empty list contributes no entry and no bytes). -/
theorem entries_getExecutionRequestsList (r : Gloas.ExecutionRequests) :
    ((Gloas.getExecutionRequestsList r).filterMap (entryOf 3)).flatten = Ssz.serialize r.builder_deposits ∧
      ((Gloas.getExecutionRequestsList r).filterMap (entryOf 4)).flatten = Ssz.serialize r.builder_exits := by
  unfold Gloas.getExecutionRequestsList
  rw [entries_filterMap, entries_filterMap]
  simp only [List.filter_cons, List.filter_nil, JauneConsensus.depositRequestType,
    JauneConsensus.withdrawalRequestType, JauneConsensus.consolidationRequestType,
    Gloas.builderDepositRequestType, Gloas.builderExitRequestType,
    eq_false (by decide : ¬((0 : UInt8) = 3)), eq_false (by decide : ¬((1 : UInt8) = 3)),
    eq_false (by decide : ¬((2 : UInt8) = 3)), eq_false (by decide : ¬((4 : UInt8) = 3)),
    eq_false (by decide : ¬((0 : UInt8) = 4)), eq_false (by decide : ¬((1 : UInt8) = 4)),
    eq_false (by decide : ¬((2 : UInt8) = 4)), eq_false (by decide : ¬((3 : UInt8) = 4)),
    decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, and_self]

/-- **The deposit records of a Gloas payload's block.** A kept block whose output requests are
`get_execution_requests_list r` emits, as type-3 records, exactly the serializations of `r`'s builder
deposits, in order. -/
theorem deposit_blockEmissions {b : KeptBlock} {r : Gloas.ExecutionRequests}
    (h : b.output.requests = Gloas.getExecutionRequestsList r) :
    Deposit.Indexed.blockEmissions b = r.builder_deposits.toArray.toList.map Ssz.serialize := by
  show Blanc.List.chunksOf 184 (blockDelivered 3 b) = _
  rw [blockDelivered, h, (entries_getExecutionRequestsList r).1,
    serialize_progressiveList_of_fixedSize (k := 184) rfl]
  exact Blanc.List.chunksOf_flatMap (by decide) _ _ fun x _ => serialize_builderDepositRequest_length x

/-- **The exit records of a Gloas payload's block.** As `deposit_blockEmissions`, for type-4 records and the
builder exits. -/
theorem exit_blockEmissions {b : KeptBlock} {r : Gloas.ExecutionRequests}
    (h : b.output.requests = Gloas.getExecutionRequestsList r) :
    Exit.Indexed.blockEmissions b = r.builder_exits.toArray.toList.map Ssz.serialize := by
  show Blanc.List.chunksOf 68 (blockDelivered 4 b) = _
  rw [blockDelivered, h, (entries_getExecutionRequestsList r).2,
    serialize_progressiveList_of_fixedSize (k := 68) rfl]
  exact Blanc.List.chunksOf_flatMap (by decide) _ _ fun x _ => serialize_builderExitRequest_length x

end Blanc.Lift.BuilderRequest.RequestCodecG
