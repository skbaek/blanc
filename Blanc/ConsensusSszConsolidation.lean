import Blanc.ConsensusSsz

/-!
# SSZ bytes of consensus consolidation requests

The actual consensus container is three fixed-size fields, in source-address,
source-key, target-key order. Its 116 bytes determine all three fields.
-/

namespace Blanc.ConsensusSsz

open Jaune JauneConsensus

/-- The actual consolidation container serializes as its three fixed-size fields. -/
theorem serialize_consolidationRequest (cr : ConsolidationRequest) :
    Ssz.serialize cr = cr.source_address.toBytes ++
      cr.source_pubkey.toArray.toList ++ cr.target_pubkey.toArray.toList := by
  change serializeParts [fieldPart cr.source_address, fieldPart cr.source_pubkey,
    fieldPart cr.target_pubkey] = _
  simp only [fieldPart]
  rw [show Ssz.fixedSize? Adr = some 20 from rfl,
    show Ssz.fixedSize? BLSPubkey = some 48 from rfl]
  have fixed := serializeParts_fixed (fun b : Bytes => b)
    [Ssz.serialize cr.source_address, Ssz.serialize cr.source_pubkey,
      Ssz.serialize cr.target_pubkey]
  simp only [List.map] at fixed
  rw [fixed, serialize_byteVector, serialize_byteVector]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-- A consolidation request contains exactly 116 SSZ bytes. -/
theorem serialize_consolidationRequest_length (cr : ConsolidationRequest) :
    (Ssz.serialize cr).length = 116 := by
  rw [serialize_consolidationRequest]
  simp only [List.length_append, Array.length_toList,
    cr.source_pubkey.size_eq, cr.target_pubkey.size_eq]
  rfl

/-- The actual consolidation request serialization is injective. -/
theorem serialize_consolidationRequest_injective :
    Function.Injective (Ssz.serialize : ConsolidationRequest → Bytes) := by
  intro a b h
  rw [serialize_consolidationRequest, serialize_consolidationRequest] at h
  obtain ⟨h, ht⟩ := List.append_inj h (by
    simp only [List.length_append, Array.length_toList,
      a.source_pubkey.size_eq, b.source_pubkey.size_eq]
    rfl)
  obtain ⟨ha, hs⟩ := List.append_inj h rfl
  obtain ⟨a₀, a₁, a₂⟩ := a
  obtain ⟨b₀, b₁, b₂⟩ := b
  obtain rfl := adr_toBytes_injective ha
  obtain rfl := SszVector.ext (Array.toList_inj.mp hs)
  obtain rfl := SszVector.ext (Array.toList_inj.mp ht)
  rfl

/-- The first 20 serialized bytes are the request's source address. -/
theorem serialize_consolidationRequest_take20 (cr : ConsolidationRequest) :
    (Ssz.serialize cr).take 20 = cr.source_address.toBytes := by
  rw [serialize_consolidationRequest, List.append_assoc,
    List.take_append_of_le_length (show 20 ≤ cr.source_address.toBytes.length from Nat.le_refl 20),
    List.take_of_length_le (show cr.source_address.toBytes.length ≤ 20 from Nat.le_refl 20)]

end Blanc.ConsensusSsz
