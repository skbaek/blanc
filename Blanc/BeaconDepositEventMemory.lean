import Blanc.BeaconDepositAbiMemory
import Blanc.BeaconDepositMemory
import Blanc.BytesWrite

/-!
# Beacon deposit event memory

Symbolic memory images for the successful `DepositEvent` staging path.  The
definitions follow the executable write order exactly, while the carrier below
exposes only the canonical 576-byte log image and the two retained words used
by the later hash and insertion phases.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-- Decoder memory after the amount-in-gwei word has been retained. -/
def depositEventInputMemory (data : Bytes) (amount : B256) : Mem :=
  (depositDecodedMemory data).write 672 amount.toBytes

/-- Symbolic image corresponding to `depositEventInputMemory`. -/
def depositEventInputImage (data : Bytes) (amount : B256) : Bytes :=
  Bytes.writeAt (depositDecodedImage data) 672 amount.toBytes

/-- Decoder reads retained alongside the source amount word. -/
structure DepositEventInputMemoryCarrier
    (memory : Mem) (data : Bytes) (amount : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 704
  size_mod : memory.size % 32 = 0
  image_length : image.length = 704
  offset0_read : image.sliceD 0 32 0 =
    (depositOffsetWord data 0).toBytes
  offset1_read : image.sliceD 32 32 0 =
    (depositOffsetWord data 1).toBytes
  offset2_read : image.sliceD 64 32 0 =
    (depositOffsetWord data 2).toBytes
  amount_read : image.sliceD 672 32 0 = amount.toBytes

/-- The concrete decoder-plus-amount image satisfies the event input carrier. -/
def depositEventInputMemory_carrier (data : Bytes) (amount : B256) :
    DepositEventInputMemoryCarrier
      (depositEventInputMemory data amount) data amount := by
  let hdec := depositDecodedMemory_carrier data
  have hwf : Mem.Wf (depositEventInputMemory data amount) := by
    exact hdec.wf.write _ _
  have hreads : Mem.Reads (depositEventInputMemory data amount)
      (depositEventInputImage data amount) := by
    exact Mem.Reads.write hdec.wf hdec.reads _ _
  have hsize : (depositEventInputMemory data amount).size = 704 := by
    unfold depositEventInputMemory
    rw [Mem.size_write_word_at, hdec.size_eq]
    decide +kernel
  have hlen : (depositEventInputImage data amount).length = 704 := by
    unfold depositEventInputImage
    rw [Bytes.length_writeAt, ← hdec.image_eq, hdec.image_length,
      B256.length_toBytes]
    decide +kernel
  have hoffset0 : (depositEventInputImage data amount).sliceD 0 32 0 =
      (depositOffsetWord data 0).toBytes := by
    unfold depositEventInputImage
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact hdec.offset0_read
  have hoffset1 : (depositEventInputImage data amount).sliceD 32 32 0 =
      (depositOffsetWord data 1).toBytes := by
    unfold depositEventInputImage
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact hdec.offset1_read
  have hoffset2 : (depositEventInputImage data amount).sliceD 64 32 0 =
      (depositOffsetWord data 2).toBytes := by
    unfold depositEventInputImage
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact hdec.offset2_read
  have hamount : (depositEventInputImage data amount).sliceD 672 32 0 =
      amount.toBytes := by
    unfold depositEventInputImage
    rw [show 32 = amount.toBytes.length by rw [B256.length_toBytes]]
    exact Bytes.sliceD_writeAt _ _ _
  exact ⟨depositEventInputImage data amount, hwf, hreads, hsize,
    by rw [hsize], hlen, hoffset0, hoffset1, hoffset2, hamount⟩

private structure EventMemoryImage (memory : Mem) (image : Bytes) : Prop where
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 704
  image_length : image.length = 704

private theorem EventMemoryImage.write
    {memory : Mem} {image : Bytes}
    (h : EventMemoryImage memory image) (n : Nat) (ys : Bytes)
    (hfit : n + ys.length ≤ 704) :
    EventMemoryImage (memory.write n ys) (Bytes.writeAt image n ys) := by
  have hsize : (memory.write n ys).size = 704 := by
    rw [Mem.size_write_of_le (by rw [h.size_eq]; exact hfit), h.size_eq]
  have hlen : (Bytes.writeAt image n ys).length = 704 := by
    rw [Bytes.length_writeAt, h.image_length]
    omega
  exact ⟨h.wf.write _ _, Mem.Reads.write h.wf h.reads _ _, hsize, hlen⟩

private theorem EventMemoryImage.storeLe64
    {memory : Mem} {image : Bytes}
    (h : EventMemoryImage memory image) (base : Nat) (word : B256)
    (hfit : base + 8 ≤ 704) :
    EventMemoryImage (storeLe64Memory memory base word)
      (storeLe64Image image base word) := by
  have hinv := storeLe64Memory_inv
    (base := base) (word := word) h.wf h.reads
  have hsize : (storeLe64Memory memory base word).size = 704 := by
    rw [storeLe64Memory_size_of_le (by rw [h.size_eq]; exact hfit),
      h.size_eq]
  have hle64 : (le64 word.toNat).length = 8 := rfl
  have hlen : (storeLe64Image image base word).length = 704 := by
    rw [storeLe64Image_eq_le64, Bytes.length_writeAt,
      h.image_length, hle64]
    omega
  exact ⟨hinv.1, hinv.2, hsize, hlen⟩

private theorem Bytes.sliceD_writeAt_inside_event
    (bs xs : Bytes) (start len n : Nat)
    (hstart : n ≤ start)
    (hend : start + len ≤ n + xs.length) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      xs.sliceD (start - n) len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt, if_pos (by omega)]
  congr 1
  omega

private theorem Bytes.sliceD_writeAt_extend_event
    {bs pre xs : Bytes} {n : Nat}
    (hpre : bs.sliceD 0 n 0 = pre) :
    (Bytes.writeAt bs n xs).sliceD 0 (n + xs.length) 0 =
      pre ++ xs := by
  rw [List.sliceD_add _ 0 n 0 xs.length,
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Nat.zero_add, hpre, Bytes.sliceD_writeAt]

private theorem Bytes.sliceD_join_event
    {bs left right : Bytes} {start lenLeft lenRight : Nat}
    (hleft : bs.sliceD start lenLeft 0 = left)
    (hright : bs.sliceD (start + lenLeft) lenRight 0 = right) :
    bs.sliceD start (lenLeft + lenRight) 0 = left ++ right := by
  rw [List.sliceD_add _ 0 lenLeft start lenRight, hleft, hright]

private theorem Bytes.sliceD_zeroThenLe64_event
    (bs : Bytes) (base : Nat) (word : B256) :
    (Bytes.writeAt
      (Bytes.writeAt bs base (0 : B256).toBytes)
      base (le64 word.toNat)).sliceD base 32 0 =
        le64 word.toNat ++ zeros 24 := by
  have hleft :
      (Bytes.writeAt
        (Bytes.writeAt bs base (0 : B256).toBytes)
        base (le64 word.toNat)).sliceD base 8 0 =
          le64 word.toNat := by
    simpa only [show (le64 word.toNat).length = 8 by rfl] using
      Bytes.sliceD_writeAt
        (Bytes.writeAt bs base (0 : B256).toBytes)
        (le64 word.toNat) base
  have hright :
      (Bytes.writeAt
        (Bytes.writeAt bs base (0 : B256).toBytes)
        base (le64 word.toNat)).sliceD (base + 8) 24 0 =
          zeros 24 := by
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      change base + 8 ≤ base + 8
      omega)]
    rw [Bytes.sliceD_writeAt_inside_event _ _ _ _ _ (by omega) (by
      rw [B256.length_toBytes])]
    rw [show base + 8 - base = 8 by omega]
    decide +kernel
  exact Bytes.sliceD_join_event hleft hright

def depositEventPubkeySlice (data : Bytes) : Bytes :=
  data.sliceD (36 + dynamicOffset data 0) 48 0

def depositEventWithdrawalSlice (data : Bytes) : Bytes :=
  data.sliceD (36 + dynamicOffset data 1) 32 0

def depositEventSignatureSlice (data : Bytes) : Bytes :=
  data.sliceD (36 + dynamicOffset data 2) 96 0

private theorem depositEventPubkeyRegion
    (image : Bytes) (data : Bytes) :
    (Bytes.writeAt
      (Bytes.writeAt image 224 (0 : B256).toBytes)
      192 (depositEventPubkeySlice data)).sliceD 192 64 0 =
        depositEventPubkeySlice data ++ zeros 16 := by
  have hpubkeyLength : (depositEventPubkeySlice data).length = 48 := by
    simp only [depositEventPubkeySlice, List.length_sliceD]
  have hleft :
      (Bytes.writeAt
        (Bytes.writeAt image 224 (0 : B256).toBytes)
        192 (depositEventPubkeySlice data)).sliceD 192 48 0 =
          depositEventPubkeySlice data := by
    simpa only [hpubkeyLength] using
      Bytes.sliceD_writeAt
        (Bytes.writeAt image 224 (0 : B256).toBytes)
        (depositEventPubkeySlice data) 192
  have hright :
      (Bytes.writeAt
        (Bytes.writeAt image 224 (0 : B256).toBytes)
        192 (depositEventPubkeySlice data)).sliceD 240 16 0 =
          zeros 16 := by
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [hpubkeyLength])]
    rw [Bytes.sliceD_writeAt_inside_event _ _ _ _ _
      (by omega) (by rw [B256.length_toBytes])]
    decide +kernel
  exact Bytes.sliceD_join_event hleft hright

private structure EventPayloadRegions
    (image : Bytes) (data : Bytes) : Prop where
  pubkey : image.sliceD 192 64 0 =
    depositEventPubkeySlice data ++ zeros 16
  withdrawal : image.sliceD 288 32 0 =
    depositEventWithdrawalSlice data
  signature : image.sliceD 416 96 0 =
    depositEventSignatureSlice data

private theorem EventPayloadRegions.writeBefore
    {image : Bytes} {data : Bytes}
    (h : EventPayloadRegions image data)
    (n : Nat) (xs : Bytes) (hfit : n + xs.length ≤ 192) :
    EventPayloadRegions (Bytes.writeAt image n xs) data := by
  constructor
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _ hfit]
    exact h.pubkey
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by omega)]
    exact h.withdrawal
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by omega)]
    exact h.signature

private theorem eventPayloadRegions_staged
    (image : Bytes) (data : Bytes) :
    EventPayloadRegions
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt image 224 (0 : B256).toBytes)
            192 (depositEventPubkeySlice data))
          288 (depositEventWithdrawalSlice data))
        416 (depositEventSignatureSlice data)) data := by
  let I1 := Bytes.writeAt image 224 (0 : B256).toBytes
  let I2 := Bytes.writeAt I1 192 (depositEventPubkeySlice data)
  let I3 := Bytes.writeAt I2 288 (depositEventWithdrawalSlice data)
  let I4 := Bytes.writeAt I3 416 (depositEventSignatureSlice data)
  have hpubkey2 : I2.sliceD 192 64 0 =
      depositEventPubkeySlice data ++ zeros 16 := by
    simpa only [I2, I1] using depositEventPubkeyRegion image data
  have hpubkey4 : I4.sliceD 192 64 0 =
      depositEventPubkeySlice data ++ zeros 16 := by
    dsimp only [I4, I3]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact hpubkey2
  have hwithdrawal3 : I3.sliceD 288 32 0 =
      depositEventWithdrawalSlice data := by
    dsimp only [I3]
    simpa only [depositEventWithdrawalSlice, List.length_sliceD] using
      Bytes.sliceD_writeAt I2 (depositEventWithdrawalSlice data) 288
  have hwithdrawal4 : I4.sliceD 288 32 0 =
      depositEventWithdrawalSlice data := by
    dsimp only [I4]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact hwithdrawal3
  have hsignature4 : I4.sliceD 416 96 0 =
      depositEventSignatureSlice data := by
    dsimp only [I4]
    simpa only [depositEventSignatureSlice, List.length_sliceD] using
      Bytes.sliceD_writeAt I3 (depositEventSignatureSlice data) 416
  simpa only [I4, I3, I2, I1] using
    (show EventPayloadRegions I4 data from
      ⟨hpubkey4, hwithdrawal4, hsignature4⟩)

/-- Event value staged by the successful runtime path before reconstruction. -/
def stagedDepositEvent (data : Bytes) (amount oldCount : B256) : DepositEvent :=
  ⟨depositEventPubkeySlice data, depositEventWithdrawalSlice data,
    le64 amount.toNat, depositEventSignatureSlice data,
    le64 oldCount.toNat⟩

/-- Successful ABI decoding identifies the fixed-width event slices with the
model's three dynamic deposit arguments. -/
theorem stagedDepositEvent_eq_of_decodable
    {data pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot amount oldCount : B256}
    (hdec : DepositAbiDecodable data pubkey withdrawalCredentials signature
      depositDataRoot)
    (hpubkey : pubkey.length = 48)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hsignature : signature.length = 96) :
    stagedDepositEvent data amount oldCount =
      ⟨pubkey, withdrawalCredentials, le64 amount.toNat, signature,
        le64 oldCount.toNat⟩ := by
  have hlength0 : dynamicLength data 0 = 48 := by
    have h := congrArg List.length hdec.pubkey_eq
    simpa only [dynamicPayload, List.length_sliceD, hpubkey] using h
  have hlength1 : dynamicLength data 1 = 32 := by
    have h := congrArg List.length hdec.withdrawalCredentials_eq
    simpa only [dynamicPayload, List.length_sliceD, hwithdrawal] using h
  have hlength2 : dynamicLength data 2 = 96 := by
    have h := congrArg List.length hdec.signature_eq
    simpa only [dynamicPayload, List.length_sliceD, hsignature] using h
  have hpubkeyEq : depositEventPubkeySlice data = pubkey := by
    simpa only [depositEventPubkeySlice, dynamicPayload, hlength0] using
      hdec.pubkey_eq
  have hwithdrawalEq :
      depositEventWithdrawalSlice data = withdrawalCredentials := by
    simpa only [depositEventWithdrawalSlice, dynamicPayload, hlength1] using
      hdec.withdrawalCredentials_eq
  have hsignatureEq : depositEventSignatureSlice data = signature := by
    simpa only [depositEventSignatureSlice, dynamicPayload, hlength2] using
      hdec.signature_eq
  simp only [stagedDepositEvent, hpubkeyEq, hwithdrawalEq, hsignatureEq]

/-- Final memory after `stageDepositEvent`, before the following reconstruction
walk starts.  Every binding is one source instruction's memory mutation. -/
def depositEventMemory (data : Bytes) (amount oldCount : B256) : Mem :=
  let M0 := depositEventInputMemory data amount
  let M1 := M0.write 224 (0 : B256).toBytes
  let M2 := M1.write 192 (depositEventPubkeySlice data)
  let M3 := M2.write 288 (depositEventWithdrawalSlice data)
  let M4 := M3.write 416 (depositEventSignatureSlice data)
  let M5 := M4.write 0 (160 : B256).toBytes
  let M6 := M5.write 32 (256 : B256).toBytes
  let M7 := M6.write 64 (320 : B256).toBytes
  let M8 := M7.write 96 (384 : B256).toBytes
  let M9 := M8.write 128 (512 : B256).toBytes
  let M10 := M9.write 160 (48 : B256).toBytes
  let M11 := M10.write 256 (32 : B256).toBytes
  let M12 := M11.write 320 (8 : B256).toBytes
  let M13 := M12.write 352 (0 : B256).toBytes
  let M14 := storeLe64Memory M13 352 amount
  let M15 := M14.write 384 (96 : B256).toBytes
  let M16 := M15.write 512 (8 : B256).toBytes
  let M17 := M16.write 544 (0 : B256).toBytes
  let M18 := M17.write 576 oldCount.toBytes
  storeLe64Memory M18 544 oldCount

/-- Symbolic image corresponding to `depositEventMemory`. -/
def depositEventImage (data : Bytes) (amount oldCount : B256) : Bytes :=
  let I0 := depositEventInputImage data amount
  let I1 := Bytes.writeAt I0 224 (0 : B256).toBytes
  let I2 := Bytes.writeAt I1 192 (depositEventPubkeySlice data)
  let I3 := Bytes.writeAt I2 288 (depositEventWithdrawalSlice data)
  let I4 := Bytes.writeAt I3 416 (depositEventSignatureSlice data)
  let I5 := Bytes.writeAt I4 0 (160 : B256).toBytes
  let I6 := Bytes.writeAt I5 32 (256 : B256).toBytes
  let I7 := Bytes.writeAt I6 64 (320 : B256).toBytes
  let I8 := Bytes.writeAt I7 96 (384 : B256).toBytes
  let I9 := Bytes.writeAt I8 128 (512 : B256).toBytes
  let I10 := Bytes.writeAt I9 160 (48 : B256).toBytes
  let I11 := Bytes.writeAt I10 256 (32 : B256).toBytes
  let I12 := Bytes.writeAt I11 320 (8 : B256).toBytes
  let I13 := Bytes.writeAt I12 352 (0 : B256).toBytes
  let I14 := storeLe64Image I13 352 amount
  let I15 := Bytes.writeAt I14 384 (96 : B256).toBytes
  let I16 := Bytes.writeAt I15 512 (8 : B256).toBytes
  let I17 := Bytes.writeAt I16 544 (0 : B256).toBytes
  let I18 := Bytes.writeAt I17 576 oldCount.toBytes
  storeLe64Image I18 544 oldCount

private theorem depositEventMemory_inv
    (data : Bytes) (amount oldCount : B256) :
    EventMemoryImage (depositEventMemory data amount oldCount)
      (depositEventImage data amount oldCount) := by
  let input := depositEventInputMemory_carrier data amount
  have h0 : EventMemoryImage (depositEventInputMemory data amount)
      (depositEventInputImage data amount) :=
    ⟨input.wf, input.reads, input.size_eq, input.image_length⟩
  have h1 := h0.write 224 (0 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h2 := h1.write 192 (depositEventPubkeySlice data) (by
    simp only [depositEventPubkeySlice, List.length_sliceD]
    omega)
  have h3 := h2.write 288 (depositEventWithdrawalSlice data) (by
    simp only [depositEventWithdrawalSlice, List.length_sliceD]
    omega)
  have h4 := h3.write 416 (depositEventSignatureSlice data) (by
    simp only [depositEventSignatureSlice, List.length_sliceD]
    omega)
  have h5 := h4.write 0 (160 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h6 := h5.write 32 (256 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h7 := h6.write 64 (320 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h8 := h7.write 96 (384 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h9 := h8.write 128 (512 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h10 := h9.write 160 (48 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h11 := h10.write 256 (32 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h12 := h11.write 320 (8 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h13 := h12.write 352 (0 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h14 := h13.storeLe64 352 amount (by omega)
  have h15 := h14.write 384 (96 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h16 := h15.write 512 (8 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h17 := h16.write 544 (0 : B256).toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h18 := h17.write 576 oldCount.toBytes (by
    simp only [B256.length_toBytes]
    omega)
  have h19 := h18.storeLe64 544 oldCount (by omega)
  simpa only [depositEventMemory, depositEventImage] using h19

/-- The event window produced by the exact staging write order is the canonical
five-tail ABI encoding of the staged event value. -/
theorem depositEventImage_event_read
    (data : Bytes) (amount oldCount : B256) :
    (depositEventImage data amount oldCount).sliceD 0 576 0 =
      abiDepositEvent (stagedDepositEvent data amount oldCount) := by
  let I0 := depositEventInputImage data amount
  let I1 := Bytes.writeAt I0 224 (0 : B256).toBytes
  let I2 := Bytes.writeAt I1 192 (depositEventPubkeySlice data)
  let I3 := Bytes.writeAt I2 288 (depositEventWithdrawalSlice data)
  let I4 := Bytes.writeAt I3 416 (depositEventSignatureSlice data)
  let I5 := Bytes.writeAt I4 0 (160 : B256).toBytes
  let I6 := Bytes.writeAt I5 32 (256 : B256).toBytes
  let I7 := Bytes.writeAt I6 64 (320 : B256).toBytes
  let I8 := Bytes.writeAt I7 96 (384 : B256).toBytes
  let I9 := Bytes.writeAt I8 128 (512 : B256).toBytes
  let I10 := Bytes.writeAt I9 160 (48 : B256).toBytes
  let I11 := Bytes.writeAt I10 256 (32 : B256).toBytes
  let I12 := Bytes.writeAt I11 320 (8 : B256).toBytes
  let I13 := Bytes.writeAt I12 352 (0 : B256).toBytes
  let I14 := storeLe64Image I13 352 amount
  let I15 := Bytes.writeAt I14 384 (96 : B256).toBytes
  let I16 := Bytes.writeAt I15 512 (8 : B256).toBytes
  let I17 := Bytes.writeAt I16 544 (0 : B256).toBytes
  let I18 := Bytes.writeAt I17 576 oldCount.toBytes
  let I19 := storeLe64Image I18 544 oldCount
  have hp4 : EventPayloadRegions I4 data := by
    simpa only [I4, I3, I2, I1] using
      eventPayloadRegions_staged I0 data
  have hp5 : EventPayloadRegions I5 data := by
    dsimp only [I5]
    exact hp4.writeBefore 0 (160 : B256).toBytes (by
      rw [B256.length_toBytes]
      omega)
  have hp6 : EventPayloadRegions I6 data := by
    dsimp only [I6]
    exact hp5.writeBefore 32 (256 : B256).toBytes (by
      rw [B256.length_toBytes]
      omega)
  have hp7 : EventPayloadRegions I7 data := by
    dsimp only [I7]
    exact hp6.writeBefore 64 (320 : B256).toBytes (by
      rw [B256.length_toBytes]
      omega)
  have hp8 : EventPayloadRegions I8 data := by
    dsimp only [I8]
    exact hp7.writeBefore 96 (384 : B256).toBytes (by
      rw [B256.length_toBytes]
      omega)
  have hp9 : EventPayloadRegions I9 data := by
    dsimp only [I9]
    exact hp8.writeBefore 128 (512 : B256).toBytes (by
      rw [B256.length_toBytes]
      omega)
  have hp10 : EventPayloadRegions I10 data := by
    dsimp only [I10]
    exact hp9.writeBefore 160 (48 : B256).toBytes (by
      rw [B256.length_toBytes])
  have h5 : I5.sliceD 0 32 0 = (160 : B256).toBytes := by
    dsimp only [I5]
    simpa only [B256.length_toBytes] using
      Bytes.sliceD_writeAt I4 (160 : B256).toBytes 0
  have h6 : I6.sliceD 0 64 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes := by
    dsimp only [I6]
    simpa only [B256.length_toBytes] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I5) (pre := (160 : B256).toBytes)
        (xs := (256 : B256).toBytes) (n := 32) h5)
  have h7 : I7.sliceD 0 96 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes := by
    dsimp only [I7]
    simpa only [B256.length_toBytes, List.append_assoc] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I6)
        (pre := (160 : B256).toBytes ++ (256 : B256).toBytes)
        (xs := (320 : B256).toBytes) (n := 64) h6)
  have h8 : I8.sliceD 0 128 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes := by
    dsimp only [I8]
    simpa only [B256.length_toBytes, List.append_assoc] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I7)
        (pre := (160 : B256).toBytes ++ (256 : B256).toBytes ++
          (320 : B256).toBytes)
        (xs := (384 : B256).toBytes) (n := 96) h7)
  have h9 : I9.sliceD 0 160 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes := by
    dsimp only [I9]
    simpa only [B256.length_toBytes, List.append_assoc] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I8)
        (pre := (160 : B256).toBytes ++ (256 : B256).toBytes ++
          (320 : B256).toBytes ++ (384 : B256).toBytes)
        (xs := (512 : B256).toBytes) (n := 128) h8)
  have h10 : I10.sliceD 0 192 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes := by
    dsimp only [I10]
    simpa only [B256.length_toBytes, List.append_assoc] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I9)
        (pre := (160 : B256).toBytes ++ (256 : B256).toBytes ++
          (320 : B256).toBytes ++ (384 : B256).toBytes ++
            (512 : B256).toBytes)
        (xs := (48 : B256).toBytes) (n := 160) h9)
  have h10Full : I10.sliceD 0 256 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 := by
    simpa only [List.append_assoc] using
      (Bytes.sliceD_join_event h10 hp10.pubkey)
  have h11Prefix : I11.sliceD 0 288 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes := by
    dsimp only [I11]
    simpa only [B256.length_toBytes, List.append_assoc] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I10)
        (pre := (160 : B256).toBytes ++ (256 : B256).toBytes ++
          (320 : B256).toBytes ++ (384 : B256).toBytes ++
            (512 : B256).toBytes ++ (48 : B256).toBytes ++
              depositEventPubkeySlice data ++ zeros 16)
        (xs := (32 : B256).toBytes) (n := 256) h10Full)
  have hwithdrawal11 : I11.sliceD 288 32 0 =
      depositEventWithdrawalSlice data := by
    dsimp only [I11]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes])]
    exact hp10.withdrawal
  have h11Full : I11.sliceD 0 320 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data := by
    simpa only [List.append_assoc] using
      (Bytes.sliceD_join_event h11Prefix hwithdrawal11)
  have h12Prefix : I12.sliceD 0 352 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes := by
    dsimp only [I12]
    simpa only [B256.length_toBytes, List.append_assoc] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I11)
        (pre := (160 : B256).toBytes ++ (256 : B256).toBytes ++
          (320 : B256).toBytes ++ (384 : B256).toBytes ++
            (512 : B256).toBytes ++ (48 : B256).toBytes ++
              depositEventPubkeySlice data ++ zeros 16 ++
                (32 : B256).toBytes ++ depositEventWithdrawalSlice data)
        (xs := (8 : B256).toBytes) (n := 320) h11Full)
  have h14Prefix : I14.sliceD 0 352 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes := by
    dsimp only [I14, I13]
    rw [storeLe64Image_eq_le64,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h12Prefix
  have hamountPayload : I14.sliceD 352 32 0 =
      le64 amount.toNat ++ zeros 24 := by
    dsimp only [I14, I13]
    rw [storeLe64Image_eq_le64]
    exact Bytes.sliceD_zeroThenLe64_event I12 352 amount
  have h14Full : I14.sliceD 0 384 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24 := by
    simpa only [List.append_assoc] using
      (Bytes.sliceD_join_event h14Prefix hamountPayload)
  have h15Prefix : I15.sliceD 0 416 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24 ++
                    (96 : B256).toBytes := by
    dsimp only [I15]
    simpa only [B256.length_toBytes, List.append_assoc] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I14)
        (pre := (160 : B256).toBytes ++ (256 : B256).toBytes ++
          (320 : B256).toBytes ++ (384 : B256).toBytes ++
            (512 : B256).toBytes ++ (48 : B256).toBytes ++
              depositEventPubkeySlice data ++ zeros 16 ++
                (32 : B256).toBytes ++ depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24)
        (xs := (96 : B256).toBytes) (n := 384) h14Full)
  have hsignature15 : I15.sliceD 416 96 0 =
      depositEventSignatureSlice data := by
    dsimp only [I15, I14, I13, I12, I11]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]), storeLe64Image_eq_le64,
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        change 352 + 8 ≤ 416
        omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]
        omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]
        omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]
        omega)]
    exact hp10.signature
  have h15Full : I15.sliceD 0 512 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24 ++
                    (96 : B256).toBytes ++
                      depositEventSignatureSlice data := by
    simpa only [List.append_assoc] using
      (Bytes.sliceD_join_event h15Prefix hsignature15)
  have h16Prefix : I16.sliceD 0 544 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24 ++
                    (96 : B256).toBytes ++
                      depositEventSignatureSlice data ++
                        (8 : B256).toBytes := by
    dsimp only [I16]
    simpa only [B256.length_toBytes, List.append_assoc] using
      (Bytes.sliceD_writeAt_extend_event
        (bs := I15)
        (pre := (160 : B256).toBytes ++ (256 : B256).toBytes ++
          (320 : B256).toBytes ++ (384 : B256).toBytes ++
            (512 : B256).toBytes ++ (48 : B256).toBytes ++
              depositEventPubkeySlice data ++ zeros 16 ++
                (32 : B256).toBytes ++ depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24 ++
                    (96 : B256).toBytes ++ depositEventSignatureSlice data)
        (xs := (8 : B256).toBytes) (n := 512) h15Full)
  have h19Prefix : I19.sliceD 0 544 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24 ++
                    (96 : B256).toBytes ++
                      depositEventSignatureSlice data ++
                        (8 : B256).toBytes := by
    dsimp only [I19, I18, I17]
    rw [storeLe64Image_eq_le64,
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h16Prefix
  have hindexLeft : I19.sliceD 544 8 0 = le64 oldCount.toNat := by
    dsimp only [I19]
    rw [storeLe64Image_eq_le64]
    simpa only [show (le64 oldCount.toNat).length = 8 by rfl] using
      Bytes.sliceD_writeAt I18 (le64 oldCount.toNat) 544
  have hindexRight : I19.sliceD 552 24 0 = zeros 24 := by
    dsimp only [I19, I18, I17]
    rw [storeLe64Image_eq_le64,
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        change 544 + 8 ≤ 552
        omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside_event _ _ _ _ _
        (by omega) (by rw [B256.length_toBytes])]
    decide +kernel
  have hindexPayload : I19.sliceD 544 32 0 =
      le64 oldCount.toNat ++ zeros 24 := by
    exact Bytes.sliceD_join_event hindexLeft hindexRight
  have hfinal : I19.sliceD 0 576 0 =
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24 ++
                    (96 : B256).toBytes ++
                      depositEventSignatureSlice data ++
                        (8 : B256).toBytes ++ le64 oldCount.toNat ++
                          zeros 24 := by
    simpa only [List.append_assoc] using
      (Bytes.sliceD_join_event h19Prefix hindexPayload)
  have habi :
      (160 : B256).toBytes ++ (256 : B256).toBytes ++
        (320 : B256).toBytes ++ (384 : B256).toBytes ++
          (512 : B256).toBytes ++ (48 : B256).toBytes ++
            depositEventPubkeySlice data ++ zeros 16 ++
              (32 : B256).toBytes ++
                depositEventWithdrawalSlice data ++
                  (8 : B256).toBytes ++ le64 amount.toNat ++ zeros 24 ++
                    (96 : B256).toBytes ++
                      depositEventSignatureSlice data ++
                        (8 : B256).toBytes ++ le64 oldCount.toNat ++
                          zeros 24 =
        abiDepositEvent (stagedDepositEvent data amount oldCount) := by
    have hpubkeyLength : (depositEventPubkeySlice data).length = 48 := by
      simp only [depositEventPubkeySlice, List.length_sliceD]
    have hwithdrawalLength :
        (depositEventWithdrawalSlice data).length = 32 := by
      simp only [depositEventWithdrawalSlice, List.length_sliceD]
    have hsignatureLength :
        (depositEventSignatureSlice data).length = 96 := by
      simp only [depositEventSignatureSlice, List.length_sliceD]
    simpa only [stagedDepositEvent, List.append_assoc] using
      (abiDepositEvent_fixed_layout
        (stagedDepositEvent data amount oldCount)
        hpubkeyLength hwithdrawalLength rfl hsignatureLength rfl).symm
  simpa only [depositEventImage, I19, I18, I17, I16, I15, I14, I13,
    I12, I11, I10, I9, I8, I7, I6, I5, I4, I3, I2, I1, I0] using
      hfinal.trans habi

/-- Exact memory facts consumed by reconstruction and the final log proof. -/
structure DepositEventMemoryCarrier
    (memory : Mem) (event : DepositEvent)
    (amount oldCount : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 704
  image_length : image.length = 704
  event_read : image.sliceD 0 576 0 = abiDepositEvent event
  oldCount_read : image.sliceD 576 32 0 = oldCount.toBytes
  amount_read : image.sliceD 672 32 0 = amount.toBytes

/-- The concrete event-stage memory carries its exact log image and both
register words retained for the following reconstruction. -/
def depositEventMemory_carrier
    (data : Bytes) (amount oldCount : B256) :
    DepositEventMemoryCarrier
      (depositEventMemory data amount oldCount)
      (stagedDepositEvent data amount oldCount) amount oldCount := by
  let hinv := depositEventMemory_inv data amount oldCount
  have holdCount :
      (depositEventImage data amount oldCount).sliceD 576 32 0 =
        oldCount.toBytes := by
    unfold depositEventImage
    rw [storeLe64Image_eq_le64,
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        change 544 + 8 ≤ 576
        omega)]
    simpa only [B256.length_toBytes] using
      Bytes.sliceD_writeAt
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt
              (storeLe64Image
                (Bytes.writeAt
                  (Bytes.writeAt
                    (Bytes.writeAt
                      (Bytes.writeAt
                        (Bytes.writeAt
                          (Bytes.writeAt
                            (Bytes.writeAt
                              (Bytes.writeAt
                                (Bytes.writeAt
                                  (Bytes.writeAt
                                    (Bytes.writeAt
                                      (Bytes.writeAt
                                        (Bytes.writeAt
                                          (depositEventInputImage data amount)
                                          224 (0 : B256).toBytes)
                                        192 (depositEventPubkeySlice data))
                                      288 (depositEventWithdrawalSlice data))
                                    416 (depositEventSignatureSlice data))
                                  0 (160 : B256).toBytes)
                                32 (256 : B256).toBytes)
                              64 (320 : B256).toBytes)
                            96 (384 : B256).toBytes)
                          128 (512 : B256).toBytes)
                        160 (48 : B256).toBytes)
                      256 (32 : B256).toBytes)
                    320 (8 : B256).toBytes)
                  352 (0 : B256).toBytes)
                352 amount)
              384 (96 : B256).toBytes)
            512 (8 : B256).toBytes)
          544 (0 : B256).toBytes)
        oldCount.toBytes 576
  have hamount :
      (depositEventImage data amount oldCount).sliceD 672 32 0 =
        amount.toBytes := by
    unfold depositEventImage
    simp only [storeLe64Image_eq_le64]
    repeat' first
      | rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
          simp only [B256.length_toBytes, depositEventPubkeySlice,
            depositEventWithdrawalSlice, depositEventSignatureSlice,
            List.length_sliceD, le64, List.length_cons, List.length_nil]
          omega)]
    unfold depositEventInputImage
    simpa only [B256.length_toBytes] using
      Bytes.sliceD_writeAt (depositDecodedImage data) amount.toBytes 672
  exact ⟨depositEventImage data amount oldCount, hinv.wf, hinv.reads,
    hinv.size_eq, hinv.image_length,
    depositEventImage_event_read data amount oldCount,
    holdCount, hamount⟩

end Blanc.BeaconDeposit
