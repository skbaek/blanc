import Blanc.ConsensusSsz

/-! Field equations and exact projections for the actual consensus deposit request. -/
namespace Blanc.ConsensusSsz

open Jaune JauneConsensus

/-- The actual deposit request serializes its five fields in contract-event order. -/
theorem serialize_depositRequest (dr : DepositRequest) :
    Ssz.serialize dr = dr.pubkey.toArray.toList ++ dr.withdrawal_credentials.toBytes ++
      leBytes 8 dr.amount.toNat ++ dr.signature.toArray.toList ++ leBytes 8 dr.index.toNat := by
  change serializeParts [fieldPart dr.pubkey, fieldPart dr.withdrawal_credentials,
    fieldPart dr.amount, fieldPart dr.signature, fieldPart dr.index] = _
  simp only [fieldPart]
  rw [show Ssz.fixedSize? BLSPubkey = some 48 from rfl,
    show Ssz.fixedSize? Bytes32 = some 32 from rfl,
    show Ssz.fixedSize? U64 = some 8 from rfl,
    show Ssz.fixedSize? BLSSignature = some 96 from rfl]
  have parts := serializeParts_fixed (fun b : Bytes => b)
    [Ssz.serialize dr.pubkey, Ssz.serialize dr.withdrawal_credentials,
      Ssz.serialize dr.amount, Ssz.serialize dr.signature, Ssz.serialize dr.index]
  simp only [List.map] at parts
  rw [parts, serialize_byteVector, serialize_byteVector]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-- Every actual deposit request has exactly 192 serialized bytes. -/
theorem serialize_depositRequest_length (dr : DepositRequest) :
    (Ssz.serialize dr).length = 192 := by
  rw [serialize_depositRequest]
  simp only [List.length_append, Array.length_toList, dr.pubkey.size_eq,
    dr.signature.size_eq, B256.length_toBytes, length_leBytes]

/-- The 192 bytes distinguish every field of the actual request. -/
theorem serialize_depositRequest_injective :
    Function.Injective (Ssz.serialize : DepositRequest → Bytes) := by
  intro a b h
  rw [serialize_depositRequest, serialize_depositRequest] at h
  have lengths : ∀ r : DepositRequest,
      r.pubkey.toArray.toList.length = 48 ∧ r.signature.toArray.toList.length = 96 := by
    intro r
    exact ⟨by rw [Array.length_toList, r.pubkey.size_eq],
      by rw [Array.length_toList, r.signature.size_eq]⟩
  obtain ⟨h, hi⟩ := List.append_inj h (by
    simp only [List.length_append, (lengths a).1, (lengths b).1,
      (lengths a).2, (lengths b).2, B256.length_toBytes, length_leBytes])
  obtain ⟨h, hs⟩ := List.append_inj h (by
    simp only [List.length_append, (lengths a).1, (lengths b).1,
      B256.length_toBytes, length_leBytes])
  obtain ⟨h, ha⟩ := List.append_inj h (by
    simp only [List.length_append, (lengths a).1, (lengths b).1, B256.length_toBytes])
  obtain ⟨hp, hw⟩ := List.append_inj h (by rw [(lengths a).1, (lengths b).1])
  have hw' := congrArg Bytes.toB256 hw
  rw [B256.toB256_toBytes, B256.toB256_toBytes] at hw'
  obtain ⟨ap, aw, aa, as, ai⟩ := a
  obtain ⟨bp, bw, ba, bs, bi⟩ := b
  obtain rfl := SszVector.ext (Array.toList_inj.mp hp)
  obtain rfl := hw'
  obtain rfl := leBytes_eight_injective ha
  obtain rfl := SszVector.ext (Array.toList_inj.mp hs)
  obtain rfl := leBytes_eight_injective hi
  rfl

/-- Each field is the corresponding exact byte window of the actual serialization. -/
theorem serialize_depositRequest_fields (dr : DepositRequest) :
    (Ssz.serialize dr).take 48 = dr.pubkey.toArray.toList ∧
    ((Ssz.serialize dr).drop 48).take 32 = dr.withdrawal_credentials.toBytes ∧
    ((Ssz.serialize dr).drop 80).take 8 = leBytes 8 dr.amount.toNat ∧
    ((Ssz.serialize dr).drop 88).take 96 = dr.signature.toArray.toList ∧
    (Ssz.serialize dr).drop 184 = leBytes 8 dr.index.toNat := by
  rw [serialize_depositRequest]
  simp (discharger := simp only [List.length_append, Array.length_toList,
      dr.pubkey.size_eq, dr.signature.size_eq, B256.length_toBytes, length_leBytes]; omega) only
    [List.append_assoc, List.take_append, List.drop_append, List.drop_eq_nil_of_le,
      List.take_of_length_le, List.take_zero, List.drop_zero, List.nil_append,
      List.append_nil, Array.length_toList, dr.pubkey.size_eq, dr.signature.size_eq,
      B256.length_toBytes, length_leBytes, Nat.reduceSub, and_self, eq_self]

end Blanc.ConsensusSsz
