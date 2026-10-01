import Blanc.Lift.WithdrawalRequest.SystemMemory

/-! Exact output windows of the actual eleven-write dequeue record stage. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune
open Blanc.WithdrawalRequest

private theorem record_offset (i : Nat) (hi : i < 16) :
    (systemRecordOffset i.toB256).toNat = 76 * i := by
  rw [systemRecordOffset, B256.toNat_mul, B256.toNat_toB256, Nat.lo_eq]
  change (76 * (i % 2 ^ 256)) % 2 ^ 256 = 76 * i
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
  exact Nat.mod_eq_of_lt (by omega)

private theorem record_pubkey_offset (i : Nat) (hi : i < 16) :
    (systemRecordPubkeyOffset i.toB256).toNat = 20 + 76 * i := by
  rw [systemRecordPubkeyOffset, B256.toNat_add, record_offset i hi]
  change (20 + 76 * i) % 2 ^ 256 = _
  exact Nat.mod_eq_of_lt (by omega)

private theorem record_suffix_offset (i : Nat) (hi : i < 16) :
    (systemRecordSuffixOffset i.toB256).toNat = 52 + 76 * i := by
  rw [systemRecordSuffixOffset, B256.toNat_add, record_pubkey_offset i hi]
  change (32 + (20 + 76 * i)) % 2 ^ 256 = _
  rw [Nat.mod_eq_of_lt (by omega : 32 + (20 + 76 * i) < 2 ^ 256)]
  omega

private theorem record_amount_offset (i : Nat) (hi : i < 16) :
    (systemRecordAmountOffset i.toB256).toNat = 68 + 76 * i := by
  rw [systemRecordAmountOffset, B256.toNat_add, record_suffix_offset i hi]
  change (16 + (52 + 76 * i)) % 2 ^ 256 = _
  rw [Nat.mod_eq_of_lt (by omega : 16 + (52 + 76 * i) < 2 ^ 256)]
  omega

private theorem record_amount_byte_offset (i n : Nat) (hi : i < 16) (hn : n ≤ 7) :
    (n.toB256 + systemRecordAmountOffset i.toB256).toNat = n + (68 + 76 * i) := by
  rw [B256.toNat_add, record_amount_offset i hi, B256.toNat_toB256, Nat.lo_eq]
  change ((n % 2 ^ 256) + (68 + 76 * i)) % 2 ^ 256 = _
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 256)]
  exact Nat.mod_eq_of_lt (by omega)

private theorem record_stage_nat (i : Nat) (hi : i < 16) (caller pubkey packed : B256) :
    systemRecordStage i.toB256 caller pubkey packed =
      [(76 * i, (caller <<< 96).toBytes),
       (20 + 76 * i, pubkey.toBytes),
       (52 + 76 * i, (systemPubkeyMask &&& packed).toBytes),
       (7 + (68 + 76 * i), [((packed >>> 64) >>> 56).2.2.toUInt8]),
       (6 + (68 + 76 * i), [((packed >>> 64) >>> 48).2.2.toUInt8]),
       (5 + (68 + 76 * i), [((packed >>> 64) >>> 40).2.2.toUInt8]),
       (4 + (68 + 76 * i), [((packed >>> 64) >>> 32).2.2.toUInt8]),
       (3 + (68 + 76 * i), [((packed >>> 64) >>> 24).2.2.toUInt8]),
       (2 + (68 + 76 * i), [((packed >>> 64) >>> 16).2.2.toUInt8]),
       (1 + (68 + 76 * i), [((packed >>> 64) >>> 8).2.2.toUInt8]),
       (68 + 76 * i, [(packed >>> 64).2.2.toUInt8])] := by
  have byteOffsets : ∀ n : Nat, n ≤ 7 →
      ((OfNat.ofNat n : B256) + systemRecordAmountOffset i.toB256).toNat =
        n + (68 + 76 * i) := by
    intro n hn
    exact record_amount_byte_offset i n hi hn
  simp only [systemRecordStage, systemRecordWordStage, systemRecordAmountStage,
    List.cons_append, List.nil_append, record_offset i hi, record_pubkey_offset i hi,
    record_suffix_offset i hi, record_amount_offset i hi]
  rw [byteOffsets 7 (by decide), byteOffsets 6 (by decide), byteOffsets 5 (by decide),
    byteOffsets 4 (by decide), byteOffsets 3 (by decide), byteOffsets 2 (by decide),
    byteOffsets 1 (by decide)]

private theorem record_caller_window (i : Nat) (hi : i < 16)
    (caller pubkey packed : B256) (image : Bytes) :
    (systemRecordImage i.toB256 caller pubkey packed image).sliceD (76 * i) 20 0 =
      (caller <<< 96).toBytes.take 20 := by
  let later : MemoryStage := (systemRecordStage i.toB256 caller pubkey packed).drop 1
  have stage : systemRecordStage i.toB256 caller pubkey packed =
      (76 * i, (caller <<< 96).toBytes) :: later := by
    dsimp only [later]
    rw [record_stage_nat i hi]
    rfl
  have avoids : later.avoids (76 * i) 20 = true := by
    dsimp only [later]
    rw [record_stage_nat i hi]
    simp only [List.drop_succ_cons, List.drop_zero, MemoryStage.avoids,
      List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq]
    simp only [B256.length_toBytes, List.length_cons, List.length_nil]
    repeat' apply And.intro
    all_goals first | exact True.intro | omega
  rw [systemRecordImage, stage, MemoryStage.applyImage_cons,
    MemoryStage.applyImage_sliceD_of_avoids later _ _ _ avoids]
  rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (Nat.le_refl _) (by
    rw [B256.length_toBytes]
    omega)]
  rw [Nat.sub_self]
  unfold List.sliceD
  rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega)]

private theorem record_pubkey_window (i : Nat) (hi : i < 16)
    (caller pubkey packed : B256) (image : Bytes) :
    (systemRecordImage i.toB256 caller pubkey packed image).sliceD (20 + 76 * i) 32 0 =
      pubkey.toBytes := by
  let earlier : MemoryStage := (systemRecordStage i.toB256 caller pubkey packed).take 1
  let later : MemoryStage := (systemRecordStage i.toB256 caller pubkey packed).drop 2
  have stage : systemRecordStage i.toB256 caller pubkey packed =
      earlier ++ (20 + 76 * i, pubkey.toBytes) :: later := by
    dsimp only [earlier, later]
    rw [record_stage_nat i hi]
    rfl
  have avoids : later.avoids (20 + 76 * i) 32 = true := by
    dsimp only [later]
    rw [record_stage_nat i hi]
    simp only [List.drop_succ_cons, List.drop_zero, MemoryStage.avoids,
      List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq]
    simp only [B256.length_toBytes, List.length_cons, List.length_nil]
    repeat' apply And.intro
    all_goals first | exact True.intro | omega
  rw [systemRecordImage, stage]
  exact MemoryStage.read_written earlier later image pubkey.toBytes (20 + 76 * i)
    (by simpa only [B256.length_toBytes] using avoids)

private theorem record_suffix_window (i : Nat) (hi : i < 16)
    (caller pubkey packed : B256) (image : Bytes) :
    (systemRecordImage i.toB256 caller pubkey packed image).sliceD (52 + 76 * i) 16 0 =
      packed.toBytes.take 16 := by
  let earlier : MemoryStage := (systemRecordStage i.toB256 caller pubkey packed).take 2
  let later : MemoryStage := (systemRecordStage i.toB256 caller pubkey packed).drop 3
  have stage : systemRecordStage i.toB256 caller pubkey packed =
      earlier ++ (52 + 76 * i, (systemPubkeyMask &&& packed).toBytes) :: later := by
    dsimp only [earlier, later]
    rw [record_stage_nat i hi]
    rfl
  have avoids : later.avoids (52 + 76 * i) 16 = true := by
    dsimp only [later]
    rw [record_stage_nat i hi]
    simp only [List.drop_succ_cons, List.drop_zero, MemoryStage.avoids,
      List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq]
    simp only [List.length_cons, List.length_nil]
    repeat' apply And.intro
    all_goals first | exact True.intro | omega
  rw [systemRecordImage, stage, MemoryStage.applyImage_append,
    MemoryStage.applyImage_cons,
    MemoryStage.applyImage_sliceD_of_avoids later _ _ _ avoids]
  rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (Nat.le_refl _) (by
    rw [B256.length_toBytes]
    omega), Nat.sub_self]
  unfold List.sliceD
  rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega)]
  rw [systemPubkeyMask, WordByteCodecs.high128_mask_bytes]
  rw [List.take_length_append' (by
    rw [List.length_take, B256.length_toBytes]
    rfl : (packed.toBytes.take 16).length = 16).symm]

private theorem record_amount_window (i : Nat) (hi : i < 16)
    (caller pubkey packed : B256) (image : Bytes) :
    (systemRecordImage i.toB256 caller pubkey packed image).sliceD (68 + 76 * i) 8 0 =
      [(packed >>> 64).2.2.toUInt8,
       ((packed >>> 64) >>> 8).2.2.toUInt8,
       ((packed >>> 64) >>> 16).2.2.toUInt8,
       ((packed >>> 64) >>> 24).2.2.toUInt8,
       ((packed >>> 64) >>> 32).2.2.toUInt8,
       ((packed >>> 64) >>> 40).2.2.toUInt8,
       ((packed >>> 64) >>> 48).2.2.toUInt8,
       ((packed >>> 64) >>> 56).2.2.toUInt8] := by
  let amount : Bytes := [(packed >>> 64).2.2.toUInt8,
    ((packed >>> 64) >>> 8).2.2.toUInt8,
    ((packed >>> 64) >>> 16).2.2.toUInt8,
    ((packed >>> 64) >>> 24).2.2.toUInt8,
    ((packed >>> 64) >>> 32).2.2.toUInt8,
    ((packed >>> 64) >>> 40).2.2.toUInt8,
    ((packed >>> 64) >>> 48).2.2.toUInt8,
    ((packed >>> 64) >>> 56).2.2.toUInt8]
  have byteRead : ∀ n : Nat, n < 8 →
      (systemRecordImage i.toB256 caller pubkey packed image).getD (68 + 76 * i + n) 0 =
        amount.getD n 0 := by
    intro n hn
    let earlier : MemoryStage := (systemRecordStage i.toB256 caller pubkey packed).take (10 - n)
    let later : MemoryStage := (systemRecordStage i.toB256 caller pubkey packed).drop (11 - n)
    have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    have stage : systemRecordStage i.toB256 caller pubkey packed =
        earlier ++ (68 + 76 * i + n, [amount.getD n 0]) :: later := by
      dsimp only [earlier, later]
      rw [record_stage_nat i hi]
      rw [Nat.add_comm (68 + 76 * i) n]
      rcases cases with h | h | h | h | h | h | h | h <;> subst n
      all_goals first | rfl | (rw [Nat.zero_add]; rfl)
    have avoids : later.avoids (68 + 76 * i + n) 1 = true := by
      dsimp only [later]
      rw [record_stage_nat i hi]
      rcases cases with h | h | h | h | h | h | h | h <;> subst n
      all_goals
        simp only [Nat.reduceSub, List.drop_succ_cons, List.drop_zero, MemoryStage.avoids,
          List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq]
      all_goals
        simp only [List.length_cons, List.length_nil]
        repeat' apply And.intro
        all_goals first | exact True.intro | omega
    have window := MemoryStage.read_written earlier later image [amount.getD n 0]
      (68 + 76 * i + n) (by simpa only [List.length_cons, List.length_nil] using avoids)
    rw [← stage] at window
    have value := congrArg (fun xs : Bytes => xs.getD 0 0) window
    rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by change 0 < 1; decide), Nat.add_zero] at value
    simpa only [List.getD_cons_zero, systemRecordImage] using value
  change _ = amount
  rw [List.sliceD_eq_map]
  apply List.ext_get
  · simp only [List.length_map, List.length_range]
    rfl
  · intro n hn hnAmount
    simp only [List.length_map, List.length_range] at hn
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    rw [byteRead n hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnAmount]
    rfl

private theorem packed_amount_window (entry : Entry) :
    ((pubkeyAmountWord entry).toBytes.sliceD 16 8 0).reverse =
      entry.amount.toBytes.reverse := by
  have suffixLength : (entry.pubkey.val.drop 32).length = 16 := by
    rw [List.length_drop, entry.pubkey.property]
  rw [pubkeyAmountWord_bytes, pubkeyAmountBytes, ← suffixLength,
    ← UInt64.length_toBytes entry.amount, Bytes.sliceD_append_middle]

/-- The actual eleven staged writes recover one logical 76-byte record. -/
theorem systemRecordImage_record (i : Nat) (hi : i < 16) (entry : Entry)
    (image : Bytes) :
    (systemRecordImage i.toB256 (callerWord entry) (pubkeyWord entry)
      (pubkeyAmountWord entry) image).sliceD (76 * i) 76 0 = outputRecord entry := by
  rw [show (76 : Nat) = 20 + 56 by rfl, List.sliceD_split]
  rw [record_caller_window i hi, WordByteCodecs.shift96_take20_toAdr_bytes,
    callerWord_address]
  rw [show (56 : Nat) = 32 + 24 by rfl, List.sliceD_split,
    show 76 * i + 20 = 20 + 76 * i by omega, record_pubkey_window i hi]
  rw [show (24 : Nat) = 16 + 8 by rfl, List.sliceD_split,
    show 20 + 76 * i + 32 = 52 + 76 * i by omega, record_suffix_window i hi,
    show 52 + 76 * i + 16 = 68 + 76 * i by omega, record_amount_window i hi,
    WordByteCodecs.shift64_low_bytes_reverse_slice16, packed_amount_window]
  rw [outputRecord, ← queueWords_pubkey entry]
  rw [List.append_assoc, List.append_assoc]

/-- Every staged write starts at or after the selected record. -/
theorem systemRecordImage_prefix (i : Nat) (hi : i < 16)
    (caller pubkey packed : B256) (image : Bytes) :
    (systemRecordImage i.toB256 caller pubkey packed image).sliceD 0 (76 * i) 0 =
      image.sliceD 0 (76 * i) 0 := by
  apply MemoryStage.applyImage_sliceD_of_avoids
  rw [record_stage_nat i hi]
  simp only [MemoryStage.avoids, List.all_cons, List.all_nil,
    Bool.and_eq_true, decide_eq_true_eq]
  simp only [B256.length_toBytes, List.length_cons, List.length_nil]
  repeat' apply And.intro
  all_goals first | exact True.intro | omega

/-- Extend the visible prefix without discarding the actual trailing padding. -/
theorem systemRecordImage_prefix_extend (i : Nat) (hi : i < 16) (entry : Entry)
    (image : Bytes) :
    (systemRecordImage i.toB256 (callerWord entry) (pubkeyWord entry)
      (pubkeyAmountWord entry) image).sliceD 0 (76 * (i + 1)) 0 =
      image.sliceD 0 (76 * i) 0 ++ outputRecord entry := by
  rw [show 76 * (i + 1) = 76 * i + 76 by omega, List.sliceD_split,
    Nat.zero_add, systemRecordImage_prefix i hi, systemRecordImage_record i hi]

/-- A previously represented output prefix extends by the next ordered entry. -/
theorem systemRecordImage_outputRecords (entries : List Entry) (entry : Entry)
    (image : Bytes) (hi : entries.length < 16)
    (hPrefix : image.sliceD 0 (76 * entries.length) 0 = outputRecords entries) :
    (systemRecordImage entries.length.toB256 (callerWord entry) (pubkeyWord entry)
      (pubkeyAmountWord entry) image).sliceD 0 (76 * (entries.length + 1)) 0 =
      outputRecords (entries ++ [entry]) := by
  rw [systemRecordImage_prefix_extend entries.length hi, hPrefix,
    outputRecords_append, outputRecords, outputRecords, List.append_nil]

/-- The corresponding read from actual staged memory returns the same record. -/
theorem systemRecordMemory_record (i : Nat) (hi : i < 16) (entry : Entry)
    {memory : Mem} {image : Bytes} (wf : Mem.Wf memory) (reads : Mem.Reads memory image) :
    ((systemRecordMemory i.toB256 (callerWord entry) (pubkeyWord entry)
      (pubkeyAmountWord entry) memory).read (76 * i) 76).1 = outputRecord entry := by
  rw [(systemRecordMemory_image i.toB256 (callerWord entry) (pubkeyWord entry)
    (pubkeyAmountWord entry) wf reads).2.read]
  exact systemRecordImage_record i hi entry image

end Blanc.Lift.WithdrawalRequest
