import Blanc.LidoCircuitBreakerRegistry
import Blanc.CycleWriteFree
import Blanc.TransientSettlement

/-! Pure ABI layout and bounded-offset facts for Registry enumeration. -/

namespace Blanc.LidoCircuitBreaker

open Jaune

theorem abiAddressArray_length (entries : List Entry) :
    (abiAddressArray entries).length = 64 + 32 * entries.length := by
  induction entries with
  | nil => simp [abiAddressArray, B256.length_toBytes]
  | cons entry rest ih =>
      simp [abiAddressArray, B256.length_toBytes] at ih ⊢
      omega

theorem abiAddressArray_offset_word (entries : List Entry) :
    (abiAddressArray entries).sliceD 0 32 0 = (Nat.toB256 32).toBytes := by
  unfold abiAddressArray List.sliceD
  rw [List.drop_zero, List.takeD_eq_take 0 (by simp [B256.length_toBytes])]
  change List.take 32 ((Nat.toB256 32).toBytes ++
    ((Nat.toB256 entries.length).toBytes ++
      (entries.map Prod.fst).flatMap B256.toBytes)) = _
  simpa only [B256.length_toBytes] using
    (List.take_length_append (xs := (Nat.toB256 32).toBytes)
      (ys := (Nat.toB256 entries.length).toBytes ++
        (entries.map Prod.fst).flatMap B256.toBytes))

theorem abiAddressArray_offset (entries : List Entry) :
    Bytes.toB256 ((abiAddressArray entries).sliceD 0 32 0) = Nat.toB256 32 := by
  rw [abiAddressArray_offset_word, B256.toB256_toBytes]

theorem abiAddressArray_length_word (entries : List Entry) :
    (abiAddressArray entries).sliceD 32 32 0 =
      (Nat.toB256 entries.length).toBytes := by
  unfold abiAddressArray List.sliceD
  change List.takeD 32 (List.drop 32 ((Nat.toB256 32).toBytes ++
    ((Nat.toB256 entries.length).toBytes ++
      (entries.map Prod.fst).flatMap B256.toBytes))) 0 = _
  rw [List.drop_length_append' (B256.length_toBytes _).symm,
    List.takeD_eq_take 0 (by simp [B256.length_toBytes])]
  simpa only [B256.length_toBytes] using
    (List.take_length_append (xs := (Nat.toB256 entries.length).toBytes)
      (ys := (entries.map Prod.fst).flatMap B256.toBytes))

theorem abiAddressArray_length_word_value (entries : List Entry) :
    Bytes.toB256 ((abiAddressArray entries).sliceD 32 32 0) =
      Nat.toB256 entries.length := by
  rw [abiAddressArray_length_word, B256.toB256_toBytes]

private theorem abiAddressWords_target_word (entries : List Entry)
    {i : Nat} (hi : i < entries.length) :
    ((entries.map Prod.fst).flatMap B256.toBytes).sliceD (32 * i) 32 0 =
      (entries[i].1).toBytes := by
  induction entries generalizing i with
  | nil => simp at hi
  | cons entry rest ih =>
      cases i with
      | zero =>
          unfold List.sliceD
          simp only [List.map_cons, List.flatMap_cons, Nat.mul_zero,
            List.drop_zero, List.getElem_cons_zero]
          rw [List.takeD_eq_take 0 (by simp [B256.length_toBytes])]
          simpa only [B256.length_toBytes] using
            (List.take_length_append (xs := entry.1.toBytes)
              (ys := (rest.map Prod.fst).flatMap B256.toBytes))
      | succ i =>
          have hi' : i < rest.length := by simpa using hi
          unfold List.sliceD
          simp only [List.map_cons, List.flatMap_cons, List.getElem_cons_succ]
          rw [show 32 * (i + 1) = 32 + 32 * i by omega,
            ← B256.length_toBytes entry.1, List.drop_length_add_append]
          exact ih hi'

theorem abiAddressArray_target_word (entries : List Entry)
    {i : Nat} (hi : i < entries.length) :
    (abiAddressArray entries).sliceD (64 + 32 * i) 32 0 =
      (entries[i].1).toBytes := by
  unfold abiAddressArray List.sliceD
  change List.takeD 32 (List.drop (64 + 32 * i)
    ((Nat.toB256 32).toBytes ++ ((Nat.toB256 entries.length).toBytes ++
      (entries.map Prod.fst).flatMap B256.toBytes))) 0 = _
  have hoff : (Nat.toB256 32).toBytes.length = 32 := B256.length_toBytes _
  have hlen : (Nat.toB256 entries.length).toBytes.length = 32 :=
    B256.length_toBytes _
  rw [show 64 + 32 * i = (Nat.toB256 32).toBytes.length +
      ((Nat.toB256 entries.length).toBytes.length + 32 * i) by omega,
    List.drop_length_add_append, List.drop_length_add_append]
  exact abiAddressWords_target_word entries hi

theorem abiAddressArray_target (entries : List Entry)
    {i : Nat} (hi : i < entries.length) :
    Bytes.toB256 ((abiAddressArray entries).sliceD (64 + 32 * i) 32 0) =
      entries[i].1 := by
  rw [abiAddressArray_target_word entries hi, B256.toB256_toBytes]

theorem RegistryWitness.entry_target_canonical
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {i : Nat} (hi : i < entries.length) :
    canonicalAddress entries[i].1 :=
  (h.targetsValid entries[i] (by simp)).2

theorem RegistryWitness.entry_target_lt_2pow160
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {i : Nat} (hi : i < entries.length) :
    entries[i].1.toNat < 2 ^ 160 :=
  h.entry_target_canonical hi

theorem RegistryWitness.enumeration_offsets_lt_2pow256
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {i : Nat} (hi : i < entries.length) :
    32 * i < 2 ^ 256 ∧
      64 + 32 * i < 2 ^ 256 ∧
      64 + 32 * entries.length < 2 ^ 256 ∧
      i + 1 < 2 ^ 256 := by
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.enumeration_offsets_toB256_toNat
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {i : Nat} (hi : i < entries.length) :
    (Nat.toB256 (32 * i)).toNat = 32 * i ∧
      (Nat.toB256 (64 + 32 * i)).toNat = 64 + 32 * i ∧
      (Nat.toB256 (64 + 32 * entries.length)).toNat =
        64 + 32 * entries.length ∧
      (Nat.toB256 (i + 1)).toNat = i + 1 := by
  rcases h.enumeration_offsets_lt_2pow256 hi with ⟨hword, htarget, htotal, hslot⟩
  exact ⟨B256.toNat_toB256_of_lt hword,
    B256.toNat_toB256_of_lt htarget,
    B256.toNat_toB256_of_lt htotal,
    B256.toNat_toB256_of_lt hslot⟩

theorem RegistryWitness.enumeration_word_arithmetic
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {i : Nat} (hi : i < entries.length) :
    Nat.toB256 i + 1 = Nat.toB256 (i + 1) ∧
      Nat.toB256 i * 32 = Nat.toB256 (32 * i) ∧
      Nat.toB256 (32 * i) + 64 = Nat.toB256 (64 + 32 * i) := by
  rcases h.enumeration_offsets_lt_2pow256 hi with ⟨hword, htarget, _, hslot⟩
  have hi256 : i < 2 ^ 256 := by
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  have hone : (1 : B256).toNat = 1 :=
    B256.toNat_toB256_of_lt (by norm_num)
  have h32 : (32 : B256).toNat = 32 :=
    B256.toNat_toB256_of_lt (by norm_num)
  have h64 : (64 : B256).toNat = 64 :=
    B256.toNat_toB256_of_lt (by norm_num)
  constructor
  · apply B256.toNat_inj
    have hnof : (Nat.toB256 i).Nof (1 : B256) := by
      unfold B256.Nof
      rw [B256.toNat_toB256_of_lt hi256, hone]
      exact hslot
    rw [B256.toNat_add_eq_of_nof _ _ hnof,
      B256.toNat_toB256_of_lt hi256, hone,
      B256.toNat_toB256_of_lt hslot]
  constructor
  · apply B256.toNat_inj
    rw [B256.toNat_mul, B256.toNat_toB256_of_lt hi256,
      h32, Nat.mul_comm, Nat.lo_eq_of_lt hword,
      B256.toNat_toB256_of_lt hword]
  · apply B256.toNat_inj
    have hnof : (Nat.toB256 (32 * i)).Nof (64 : B256) := by
      unfold B256.Nof
      rw [B256.toNat_toB256_of_lt hword, h64]
      omega
    rw [B256.toNat_add_eq_of_nof _ _ hnof,
      B256.toNat_toB256_of_lt hword, h64,
      B256.toNat_toB256_of_lt htarget]
    omega

theorem RegistryWitness.enumeration_covered_window
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {i : Nat} (hi : i < entries.length) :
    96 + 32 * i ≤ 64 + 32 * entries.length ∧
      64 + 32 * entries.length < 2 ^ 256 := by
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.enumeration_next_word_roundtrips
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {i : Nat} (hi : i < entries.length) :
    (Nat.toB256 (32 * (i + 1))).toNat = 32 * (i + 1) ∧
      (Nat.toB256 (64 + 32 * i)).toNat = 64 + 32 * i := by
  have hlength := h.entries_length_le
  have hnext : 32 * (i + 1) < 2 ^ 256 := by
    norm_num at hlength ⊢
    omega
  exact ⟨B256.toNat_toB256_of_lt hnext,
    B256.toNat_toB256_of_lt (h.enumeration_offsets_lt_2pow256 hi).2.1⟩

theorem RegistryWitness.enumeration_total_toB256_toNat
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) :
    (Nat.toB256 (64 + 32 * entries.length)).toNat =
      64 + 32 * entries.length := by
  apply B256.toNat_toB256_of_lt
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.enumeration_total_word_arithmetic
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) :
    (64 : B256) + 32 * Nat.toB256 entries.length =
      Nat.toB256 (64 + 32 * entries.length) := by
  have hn : entries.length < 2 ^ 256 := by
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  have hmul : 32 * entries.length < 2 ^ 256 := by
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  have htotal : 64 + 32 * entries.length < 2 ^ 256 := by
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  have h32 : (32 : B256).toNat = 32 :=
    B256.toNat_toB256_of_lt (by norm_num)
  have h64 : (64 : B256).toNat = 64 :=
    B256.toNat_toB256_of_lt (by norm_num)
  have hmulEq : (32 : B256) * Nat.toB256 entries.length =
      Nat.toB256 (32 * entries.length) := by
    apply B256.toNat_inj
    rw [B256.toNat_mul, h32, B256.toNat_toB256_of_lt hn,
      Nat.lo_eq_of_lt hmul, B256.toNat_toB256_of_lt hmul]
  rw [hmulEq]
  apply B256.toNat_inj
  have hnof : (64 : B256).Nof (Nat.toB256 (32 * entries.length)) := by
    unfold B256.Nof
    rw [h64, B256.toNat_toB256_of_lt hmul]
    omega
  rw [B256.toNat_add_eq_of_nof _ _ hnof, h64,
    B256.toNat_toB256_of_lt hmul,
    B256.toNat_toB256_of_lt htotal]

/-- The byte image produced by the two ABI header stores. -/
def enumHeaderImage (entries : List Entry) : Bytes :=
  Bytes.writeAt (Bytes.writeAt [] 0 (Nat.toB256 32).toBytes) 32
    (Nat.toB256 entries.length).toBytes

/-- The ordered image after storing an already-enumerated target prefix. -/
def enumPrefixImage (entries done : List Entry) : Bytes :=
  done.foldl (fun image entry => Bytes.writeAt image image.length entry.1.toBytes)
    (enumHeaderImage entries)

theorem enumPrefixImage_append (entries done : List Entry) (entry : Entry) :
    enumPrefixImage entries (done ++ [entry]) =
      Bytes.writeAt (enumPrefixImage entries done)
        (enumPrefixImage entries done).length entry.1.toBytes := by
  simp [enumPrefixImage]

/-- The concrete memory recurrence, rooted at `Mem.empty`, for the same stores. -/
def enumPrefixMemory (entries done : List Entry) : Mem :=
  done.foldl (fun memory entry => memory.write memory.size entry.1.toBytes)
    ((Mem.empty.write 0 (Nat.toB256 32).toBytes).write 32
      (Nat.toB256 entries.length).toBytes)

private theorem enumHeaderMemory_wf (entries : List Entry) :
    Mem.Wf (enumPrefixMemory entries []) := by
  unfold enumPrefixMemory
  apply Mem.Wf.write
  apply Mem.Wf.write
  exact Mem.wf_empty

private theorem enumHeaderMemory_size (entries : List Entry) :
    (enumPrefixMemory entries []).size = 64 := by
  unfold enumPrefixMemory
  simp only [List.foldl_nil]
  have hfirst : (Mem.empty.write 0 (Nat.toB256 32).toBytes).size = 32 :=
    Mem.size_write_word
  rw [Mem.size_write_word_at,
    if_neg (by rw [hfirst]; omega)]
  rfl

private theorem enumHeaderMemory_reads (entries : List Entry) :
    Mem.Reads (enumPrefixMemory entries []) (enumHeaderImage entries) := by
  unfold enumPrefixMemory enumHeaderImage
  have h0 := Mem.Reads.write Mem.wf_empty Mem.reads_empty 0
    (Nat.toB256 32).toBytes
  have hwf : Mem.Wf (Mem.empty.write 0 (Nat.toB256 32).toBytes) :=
    Mem.Wf.write Mem.wf_empty _ _
  exact Mem.Reads.write hwf h0 32 (Nat.toB256 entries.length).toBytes

private theorem enumHeaderImage_length (entries : List Entry) :
    (enumHeaderImage entries).length = 64 := by
  unfold enumHeaderImage
  rw [Bytes.writeAt_zero_of_le (by simp),
    Bytes.writeAt_of_length_eq (by simp [B256.length_toBytes])]
  simp [B256.length_toBytes]

private theorem enumMemory_write_next_size (memory : Mem) (entry : Entry)
    (n : Nat) (hsize : memory.size = 64 + 32 * n) :
    (memory.write (64 + 32 * n) entry.1.toBytes).size = 64 + 32 * (n + 1) := by
  rw [Mem.size_write_word_at, if_neg (by rw [hsize]; omega)]
  unfold ceil32
  rw [show (64 + 32 * n + 32) % 32 = 0 by omega]
  rfl

private theorem enumMemory_fold
    (done : List Entry) (memory : Mem) (image : Bytes) (n : Nat)
    (hwf : Mem.Wf memory) (hsize : memory.size = 64 + 32 * n)
    (himage : image.length = 64 + 32 * n) (hreads : Mem.Reads memory image) :
    Mem.Wf (done.foldl (fun μ entry => μ.write μ.size entry.1.toBytes) memory) ∧
      (done.foldl (fun μ entry => μ.write μ.size entry.1.toBytes) memory).size =
        64 + 32 * (n + done.length) ∧
      Mem.Reads (done.foldl (fun μ entry => μ.write μ.size entry.1.toBytes) memory)
        (done.foldl (fun bs entry => Bytes.writeAt bs bs.length entry.1.toBytes) image) := by
  induction done generalizing memory image n with
  | nil => exact ⟨hwf, hsize, hreads⟩
  | cons entry rest ih =>
      have hnextwf : Mem.Wf (memory.write memory.size entry.1.toBytes) :=
        Mem.Wf.write hwf _ _
      have hnextsize : (memory.write memory.size entry.1.toBytes).size =
          64 + 32 * (n + 1) := by
        rw [hsize]
        exact enumMemory_write_next_size memory entry n hsize
      have himage' : (Bytes.writeAt image image.length entry.1.toBytes).length =
          64 + 32 * (n + 1) := by
        rw [Bytes.writeAt_length, List.length_append, B256.length_toBytes, himage]
        omega
      have hnextreads : Mem.Reads (memory.write memory.size entry.1.toBytes)
          (Bytes.writeAt image image.length entry.1.toBytes) := by
        rw [hsize, ← himage]
        exact Mem.Reads.write hwf hreads image.length entry.1.toBytes
      simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (memory.write memory.size entry.1.toBytes)
          (Bytes.writeAt image image.length entry.1.toBytes) (n + 1)
          hnextwf hnextsize himage' hnextreads

theorem enumPrefixMemory_invariant (entries done : List Entry) :
    Mem.Wf (enumPrefixMemory entries done) ∧
      (enumPrefixMemory entries done).size = 64 + 32 * done.length ∧
      Mem.Reads (enumPrefixMemory entries done) (enumPrefixImage entries done) := by
  simpa [enumPrefixMemory, enumPrefixImage] using
    enumMemory_fold done (enumPrefixMemory entries []) (enumHeaderImage entries) 0
      (enumHeaderMemory_wf entries)
    (by simpa using enumHeaderMemory_size entries)
    (by simpa using enumHeaderImage_length entries)
    (enumHeaderMemory_reads entries)

private theorem enumImage_fold (done : List Entry) (image : Bytes) :
    done.foldl (fun bs entry => Bytes.writeAt bs bs.length entry.1.toBytes) image =
      image ++ (done.map Prod.fst).flatMap B256.toBytes := by
  induction done generalizing image with
  | nil => simp
  | cons entry rest ih =>
      rw [List.foldl, ih, Bytes.writeAt_length]
      simp only [List.map_cons, List.flatMap_cons, List.append_assoc]

theorem enumPrefixImage_closed (entries done : List Entry) :
    enumPrefixImage entries done =
      enumHeaderImage entries ++ (done.map Prod.fst).flatMap B256.toBytes := by
  unfold enumPrefixImage
  exact enumImage_fold done _

theorem enumHeaderImage_closed (entries : List Entry) :
    enumHeaderImage entries =
      (Nat.toB256 32).toBytes ++ (Nat.toB256 entries.length).toBytes := by
  unfold enumHeaderImage
  rw [Bytes.writeAt_zero_of_le (by simp),
    Bytes.writeAt_of_length_eq (by simp [B256.length_toBytes])]

theorem enumPrefixImage_full (entries : List Entry) :
    enumPrefixImage entries entries = abiAddressArray entries := by
  rw [enumPrefixImage_closed, enumHeaderImage_closed]
  rfl

theorem enumPrefixMemory_full_read (entries : List Entry) :
    ((enumPrefixMemory entries entries).read 0 (64 + 32 * entries.length)).1 =
      abiAddressArray entries := by
  rw [Mem.Reads.read (enumPrefixMemory_invariant entries entries).2.2,
    enumPrefixImage_full, List.sliceD]
  rw [List.drop_zero, List.takeD_eq_self 0 (abiAddressArray_length entries).symm]

theorem enumPrefixMemory_append (entries done : List Entry) (entry : Entry) :
    enumPrefixMemory entries (done ++ [entry]) =
      (enumPrefixMemory entries done).write (64 + 32 * done.length) entry.1.toBytes := by
  unfold enumPrefixMemory
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
    show (List.foldl (fun memory entry => memory.write memory.size entry.1.toBytes)
      ((Mem.empty.write 0 (Nat.toB256 32).toBytes).write 32
        (Nat.toB256 entries.length).toBytes) done).size = 64 + 32 * done.length by
      simpa [enumPrefixMemory] using (enumPrefixMemory_invariant entries done).2.1]

theorem targetAt_append_cons_length (done rest : List Entry) (entry : Entry) :
    targetAt (done ++ entry :: rest) done.length = entry.1 := by
  induction done with
  | nil => simp [targetAt]
  | cons head done ih =>
      simp only [List.cons_append, List.length_cons, targetAt]
      exact ih

set_option maxHeartbeats 400000

theorem enumPrefixMemory_read_length_fst (entries done : List Entry) :
    ((enumPrefixMemory entries done).read 32 32).1 =
      (Nat.toB256 entries.length).toBytes := by
  rw [Mem.Reads.read (enumPrefixMemory_invariant entries done).2.2,
    enumPrefixImage_closed, enumHeaderImage_closed]
  unfold List.sliceD
  rw [List.append_assoc]
  rw [List.drop_length_append'
    (xs := (Nat.toB256 32).toBytes)
    (ys := (Nat.toB256 entries.length).toBytes ++
      (done.map Prod.fst).flatMap B256.toBytes)
    (by simp [B256.length_toBytes])]
  rw [List.takeD_eq_take _ (by simp [B256.length_toBytes])]
  rw [List.take_length_append'
    (xs := (Nat.toB256 entries.length).toBytes)
    (ys := (done.map Prod.fst).flatMap B256.toBytes)
    (by simp [B256.length_toBytes])]

theorem enumPrefixMemory_read_length_snd (entries done : List Entry) :
    ((enumPrefixMemory entries done).read 32 32).2 =
      enumPrefixMemory entries done := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [(enumPrefixMemory_invariant entries done).2.1]
    omega
  · rw [(enumPrefixMemory_invariant entries done).2.1]
    omega

theorem enumPrefixMemory_extCost_length (base : Devm) (stack : List B256)
    (entries done : List Entry) (G : Nat) :
    (base.setMach ⟨stack, enumPrefixMemory entries done, G⟩).extCost
      [⟨32, 32⟩] = 0 := by
  apply Devm.extCost_zero_of_le
  · rw [(enumPrefixMemory_invariant entries done).2.1]
    omega
  · rw [(enumPrefixMemory_invariant entries done).2.1]
    omega

theorem enumPrefixMemory_extCost_full (base : Devm) (stack : List B256)
    (entries : List Entry) (G : Nat) :
    (base.setMach ⟨stack, enumPrefixMemory entries entries, G⟩).extCost
      [⟨0, 64 + 32 * entries.length⟩] = 0 := by
  apply Devm.extCost_zero_of_le
  · rw [(enumPrefixMemory_invariant entries entries).2.1]
    omega
  · rw [(enumPrefixMemory_invariant entries entries).2.1]
    omega

theorem memExtSize_enum_next (done : List Entry) :
    memExtSize (64 + 32 * done.length) (64 + 32 * done.length) 32 =
      64 + 32 * (done.length + 1) := by
  unfold memExtSize ceilDiv
  simp only [OfNat.ofNat, Nat.reduceEqDiff, ↓reduceIte]
  rw [show (64 + 32 * done.length) % 32 = 0 by omega,
    show (64 + 32 * done.length + 32) % 32 = 0 by omega]
  simp only [ite_true]
  rw [Nat.max_eq_right] <;> omega

theorem enumPrefixMemory_extCost_next (base : Devm) (stack : List B256)
    (entries done : List Entry) (G : Nat) :
    (base.setMach ⟨stack, enumPrefixMemory entries done, G⟩).extCost
      [⟨64 + 32 * done.length, 32⟩] =
      calculateMemoryGasCost (64 + 32 * (done.length + 1)) -
        calculateMemoryGasCost (64 + 32 * done.length) := by
  apply Devm.extCost_of_size (enumPrefixMemory_invariant entries done).2.1
  rw [memExtSize_enum_next]

theorem enumPrefixDevm_memRead_full (base : Devm) (entries : List Entry)
    (G : Nat) :
    (base.setMach ⟨[], enumPrefixMemory entries entries, G⟩).memRead
      0 (64 + 32 * entries.length) =
      ⟨abiAddressArray entries,
        base.setMach ⟨[], enumPrefixMemory entries entries, G⟩⟩ := by
  have hread : (enumPrefixMemory entries entries).read 0
      (64 + 32 * entries.length) =
      ⟨abiAddressArray entries, enumPrefixMemory entries entries⟩ := by
    apply Prod.ext
    · exact enumPrefixMemory_full_read entries
    · exact Mem.read_snd_eq_self (memExtSize_of_le
        (by rw [(enumPrefixMemory_invariant entries entries).2.1]; omega)
        (by rw [(enumPrefixMemory_invariant entries entries).2.1]; omega))
  unfold Devm.memRead
  rw [show (base.setMach
    ⟨[], enumPrefixMemory entries entries, G⟩).memory =
      enumPrefixMemory entries entries by rfl, hread]
  rfl

attribute [simp] enumPrefixMemory_read_length_fst
  enumPrefixMemory_read_length_snd

set_option maxHeartbeats 200000

/-- Ordered storage reads of `getPausables`: length first, then one target slot per entry. -/
def enumerationEntryKeysFrom : Nat → List Entry → List B256
  | _, [] => []
  | i, _ :: rest => arrayEntrySlot (Nat.toB256 (i + 1)) ::
      enumerationEntryKeysFrom (i + 1) rest

def enumerationStorageKeys (entries : List Entry) : List B256 :=
  arrayLengthSlot :: enumerationEntryKeysFrom 0 entries

def prepareEnumerationStorage (sevm : Sevm) (base : Devm) (entries : List Entry) : Devm :=
  (enumerationStorageKeys entries).foldl
    (fun devm key => addAccessedStorageKey devm sevm.currentTarget key) base

private theorem prewarmStorage_preserves (sevm : Sevm) (keys : List B256) (base : Devm)
    {pair : Adr × B256} (hmem : pair ∈ base.accessedStorageKeys) :
    pair ∈ (keys.foldl (fun devm key =>
      addAccessedStorageKey devm sevm.currentTarget key) base).accessedStorageKeys := by
  induction keys generalizing base with
  | nil => simpa
  | cons key rest ih =>
      apply ih
      change pair ∈ base.accessedStorageKeys.insert ⟨sevm.currentTarget, key⟩
      exact Std.HashSet.mem_insert.mpr (Or.inr hmem)

private theorem prewarmStorage_mem (sevm : Sevm) (keys : List B256) (base : Devm)
    {key : B256} (hkey : key ∈ keys) :
    (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      (keys.foldl (fun devm k =>
        addAccessedStorageKey devm sevm.currentTarget k) base).accessedStorageKeys := by
  induction keys generalizing base with
  | nil => simp at hkey
  | cons _ rest ih =>
      simp only [List.mem_cons] at hkey
      rcases hkey with rfl | hkey
      · apply prewarmStorage_preserves sevm rest
        change (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
          base.accessedStorageKeys.insert ⟨sevm.currentTarget, key⟩
        exact Std.HashSet.mem_insert_self
      · exact ih (addAccessedStorageKey base sevm.currentTarget _ ) hkey

theorem prepareEnumerationStorage_warm (sevm : Sevm) (base : Devm)
    (entries : List Entry) {key : B256} (hkey : key ∈ enumerationStorageKeys entries) :
    (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      (prepareEnumerationStorage sevm base entries).accessedStorageKeys :=
  prewarmStorage_mem sevm _ base hkey

theorem arrayLengthSlot_mem_enumerationStorageKeys (entries : List Entry) :
    arrayLengthSlot ∈ enumerationStorageKeys entries := by
  simp [enumerationStorageKeys]

theorem arrayEntrySlot_mem_enumerationEntryKeysFrom :
    ∀ (entries : List Entry) (start offset : Nat),
      offset < entries.length →
      arrayEntrySlot (Nat.toB256 (start + offset + 1)) ∈
        enumerationEntryKeysFrom start entries := by
  intro entries
  induction entries with
  | nil =>
      intro start offset h
      simp at h
  | cons entry rest ih =>
      intro start offset h
      simp only [List.length_cons] at h
      cases offset with
      | zero =>
          simp only [enumerationEntryKeysFrom, List.mem_cons]
          exact Or.inl trivial
      | succ offset =>
          simp only [enumerationEntryKeysFrom, List.mem_cons]
          apply Or.inr
          have hoff : offset < rest.length := by omega
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (start + 1) offset hoff

theorem arrayEntrySlot_mem_enumerationStorageKeys (entries : List Entry)
    (i : Nat) (hi : i < entries.length) :
    arrayEntrySlot (Nat.toB256 (i + 1)) ∈ enumerationStorageKeys entries := by
  simp only [enumerationStorageKeys, List.mem_cons]
  exact Or.inr (by simpa using
    arrayEntrySlot_mem_enumerationEntryKeysFrom entries 0 i hi)

private theorem prewarmStorage_mach (sevm : Sevm) (keys : List B256) (base : Devm) :
    (keys.foldl (fun devm key =>
      addAccessedStorageKey devm sevm.currentTarget key) base).mach = base.mach := by
  induction keys generalizing base with
  | nil => rfl
  | cons key rest ih =>
      rw [List.foldl_cons, ih]
      rfl

private theorem prewarmStorage_logs (sevm : Sevm) (keys : List B256) (base : Devm) :
    (keys.foldl (fun devm key =>
      addAccessedStorageKey devm sevm.currentTarget key) base).logs = base.logs := by
  induction keys generalizing base with
  | nil => rfl
  | cons key rest ih =>
      rw [List.foldl_cons, ih]
      rfl

private theorem prewarmStorage_state (sevm : Sevm) (keys : List B256) (base : Devm) :
    (keys.foldl (fun devm key =>
      addAccessedStorageKey devm sevm.currentTarget key) base).state = base.state := by
  induction keys generalizing base with
  | nil => rfl
  | cons key rest ih =>
      rw [List.foldl_cons, ih]
      rfl

private theorem prewarmStorage_transientStorage
    (sevm : Sevm) (keys : List B256) (base : Devm) :
    (keys.foldl (fun devm key =>
      addAccessedStorageKey devm sevm.currentTarget key) base).transientStorage =
        base.transientStorage := by
  induction keys generalizing base with
  | nil => rfl
  | cons key rest ih =>
      rw [List.foldl_cons, ih]
      rfl

theorem prepareEnumerationStorage_mach (sevm : Sevm) (base : Devm)
    (entries : List Entry) :
    (prepareEnumerationStorage sevm base entries).mach = base.mach :=
  prewarmStorage_mach sevm _ base

theorem prepareEnumerationStorage_logs (sevm : Sevm) (base : Devm)
    (entries : List Entry) :
    (prepareEnumerationStorage sevm base entries).logs = base.logs :=
  prewarmStorage_logs sevm _ base

theorem prepareEnumerationStorage_worldEq (sevm : Sevm) (base : Devm)
    (entries : List Entry) :
    Devm.WorldEq base (prepareEnumerationStorage sevm base entries) := by
  exact ⟨(prewarmStorage_state sevm _ base).symm,
    (prewarmStorage_transientStorage sevm _ base).symm⟩

/-- Warm cost for the source loop from word index `i`; each live pass owns one
memory-word expansion and the loop exit costs 49. -/
def enumLoopGasWarmFrom : Nat → List Entry → Nat
  | _, [] => 49
  | i, _ :: rest => 179 +
      (calculateMemoryGasCost (64 + 32 * (i + 1)) -
        calculateMemoryGasCost (64 + 32 * i)) +
      enumLoopGasWarmFrom (i + 1) rest

theorem enumLoopGasWarmFrom_ge (i : Nat) (entries : List Entry) :
    49 ≤ enumLoopGasWarmFrom i entries := by
  cases entries <;> simp [enumLoopGasWarmFrom]; omega

def getPausablesGasWarm (entries : List Entry) : Nat :=
  131 + calculateMemoryGasCost 64 + enumLoopGasWarmFrom 0 entries

@[simp] theorem enumLoopGasWarmFrom_nil (i : Nat) :
    enumLoopGasWarmFrom i [] = 49 := rfl

@[simp] theorem enumLoopGasWarmFrom_cons (i : Nat) (entry : Entry)
    (rest : List Entry) :
    enumLoopGasWarmFrom i (entry :: rest) =
      179 +
        (calculateMemoryGasCost (64 + 32 * (i + 1)) -
          calculateMemoryGasCost (64 + 32 * i)) +
        enumLoopGasWarmFrom (i + 1) rest := rfl

theorem getPausablesGasWarm_nil : getPausablesGasWarm [] = 186 := rfl

theorem getPausablesGasWarm_singleton (entry : Entry) :
    getPausablesGasWarm [entry] = 368 := rfl

/-- Explicit source-body resources for enumeration.  Warmth is stated for the
ordered source read-set, so it can be reused at every recursive loop step. -/
structure EnumerationResources (sevm : Sevm) (pre : Devm)
    (entries : List Entry) : Prop where
  stack_empty : pre.stack = []
  memory_empty : pre.memory = Mem.empty
  warm : ∀ key ∈ enumerationStorageKeys entries,
    (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ pre.accessedStorageKeys
  gas_sufficient : getPausablesGasWarm entries ≤ pre.gasLeft

def preparedEnumerationState (sevm : Sevm) (base : Devm)
    (entries : List Entry) : Devm :=
  (prepareEnumerationStorage sevm base entries).setMach
    ⟨[], Mem.empty, getPausablesGasWarm entries⟩

theorem enumerationResources_prepared (sevm : Sevm) (base : Devm)
    (entries : List Entry) :
    EnumerationResources sevm (preparedEnumerationState sevm base entries) entries := by
  refine ⟨rfl, rfl, ?_, Nat.le_refl _⟩
  intro key hkey
  change (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
    (prepareEnumerationStorage sevm base entries).accessedStorageKeys
  exact prepareEnumerationStorage_warm sevm base entries hkey

theorem EnumerationResources.length_warm {sevm : Sevm} {pre : Devm}
    {entries : List Entry} (h : EnumerationResources sevm pre entries) :
    (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
      pre.accessedStorageKeys :=
  h.warm _ (arrayLengthSlot_mem_enumerationStorageKeys entries)

theorem EnumerationResources.entry_warm {sevm : Sevm} {pre : Devm}
    {entries : List Entry} (h : EnumerationResources sevm pre entries)
    (i : Nat) (hi : i < entries.length) :
    (⟨sevm.currentTarget, arrayEntrySlot (Nat.toB256 (i + 1))⟩ : Adr × B256) ∈
      pre.accessedStorageKeys :=
  h.warm _ (arrayEntrySlot_mem_enumerationStorageKeys entries i hi)

theorem preparedEnumerationState_worldEq (sevm : Sevm) (base : Devm)
    (entries : List Entry) :
    Devm.WorldEq base (preparedEnumerationState sevm base entries) := by
  rcases prepareEnumerationStorage_worldEq sevm base entries with
    ⟨hstate, htransient⟩
  exact ⟨hstate, htransient⟩

theorem preparedEnumerationState_logs (sevm : Sevm) (base : Devm)
    (entries : List Entry) :
    (preparedEnumerationState sevm base entries).logs = base.logs := by
  change (prepareEnumerationStorage sevm base entries).logs = base.logs
  exact prepareEnumerationStorage_logs sevm base entries

theorem preparedEnumerationState_getCode (sevm : Sevm) (base : Devm)
    (entries : List Entry) (address : Adr) :
    (preparedEnumerationState sevm base entries).getCode address =
      base.getCode address :=
  (preparedEnumerationState_worldEq sevm base entries).getCode address |>.symm

theorem preparedEnumerationState_getStor (sevm : Sevm) (base : Devm)
    (entries : List Entry) (address : Adr) :
    Devm.getStor (preparedEnumerationState sevm base entries) address =
      Devm.getStor base address :=
  (preparedEnumerationState_worldEq sevm base entries).getStor address |>.symm

set_option maxRecDepth 4096

theorem enumLoop_pre_stack_height (base : Devm) (entries done rest : List Entry)
    (G : Nat) :
    ((base.setMach ⟨[Nat.toB256 done.length], enumPrefixMemory entries done,
      G + enumLoopGasWarmFrom done.length rest⟩).stack).length = 1 := rfl

theorem enumLoop_pre_memory_independent_of_cursor (base : Devm)
    (entries done : List Entry) (cursor cursor' G : Nat) :
    (base.setMach ⟨[Nat.toB256 cursor], enumPrefixMemory entries done, G⟩).memory =
      (base.setMach ⟨[Nat.toB256 cursor'], enumPrefixMemory entries done, G⟩).memory :=
  rfl

private theorem enumLoop_done_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (entries : List Entry) (G : Nat)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[Nat.toB256 entries.length],
        enumPrefixMemory entries entries, G + 49⟩)
      enumLoop
      ((base.setMach ⟨[], enumPrefixMemory entries entries, G⟩).withOutput
        (abiAddressArray entries)) := by
  unfold enumLoop
  have h32 : (32 : B256).toNat = 32 :=
    B256.toNat_toB256_of_lt (by norm_num)
  func_run [3, 0, 3]
  · rw [h32, enumPrefixMemory_extCost_length]
    rfl
  · rw [h32, enumPrefixMemory_read_length_fst, B256.toB256_toBytes]
    simp [B256.ltCheck]
  · rw [h32, enumPrefixMemory_read_length_snd, enumPrefixMemory_extCost_length]
    rfl
  · change G + 49 - 36 = G + 49 - 41 + gLow
    norm_num [gLow]
    omega
  · simp only [h32, enumPrefixMemory_read_length_snd,
      enumPrefixMemory_read_length_fst, B256.toB256_toBytes,
      hw.enumeration_total_word_arithmetic]
    refine Func.runCompiled_ret_of (G := G) (e := 0) rfl ?_ ?_ ?_
    · rw [hw.enumeration_total_toB256_toNat]
      exact enumPrefixMemory_extCost_full base [] entries G
    · change G + 49 - 49 = G + 0
      omega
    · rw [hw.enumeration_total_toB256_toNat]
      simpa only [Devm.setMach_setMach, Devm.memory_setMach,
        B256.toNat_zero] using
        (enumPrefixDevm_memRead_full base entries G)

/-- Exact recursive execution from an already-written prefix.  The cursor is
the sole stack word at every recursive call; the full ordered ABI image is the
eventual return, for every finite witness-valid suffix. -/
theorem enumLoop_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (entries done rest : List Entry)
    (G : Nat)
    (hsplit : entries = done ++ rest)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hwarm : ∀ key ∈ enumerationStorageKeys entries,
      (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hfs : fs[enumLoopSlot]? = some enumLoop) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[Nat.toB256 done.length],
        enumPrefixMemory entries done,
        G + enumLoopGasWarmFrom done.length rest⟩)
      enumLoop
      ((base.setMach ⟨[], enumPrefixMemory entries entries, G⟩).withOutput
        (abiAddressArray entries)) := by
  induction rest generalizing done with
  | nil =>
      simp only [List.append_nil] at hsplit
      subst entries
      exact enumLoop_done_runCompiled fs sevm base done G hw
  | cons entry rest ih =>
      unfold enumLoop
      have hdone : done.length < entries.length := by
        rw [hsplit, List.length_append, List.length_cons]
        omega
      have hkey :
          (regionWord arrayRegion).or ((1 : B256) + Nat.toB256 done.length) =
            arrayEntrySlot (Nat.toB256 (done.length + 1)) := by
        calc
          _ = (regionWord arrayRegion).or
              (Nat.toB256 done.length + (1 : B256)) := by
            rw [B256.add_comm (xs := (1 : B256))
              (ys := Nat.toB256 done.length)]
          _ = _ := by
            rw [(hw.enumeration_word_arithmetic hdone).1]
            rfl
      have hwarmKey :
          (⟨sevm.currentTarget,
            (regionWord arrayRegion).or
              ((1 : B256) + Nat.toB256 done.length)⟩ : Adr × B256) ∈
              base.accessedStorageKeys := by
        rw [hkey]
        exact hwarm _
          (arrayEntrySlot_mem_enumerationStorageKeys entries done.length hdone)
      have hvalue : base.getStorVal sevm.currentTarget
          ((regionWord arrayRegion).or
            ((1 : B256) + Nat.toB256 done.length)) = entry.1 := by
        rw [hkey]
        change (logicalStorageOfStor
          (Devm.getStor base sevm.currentTarget)).read
            (arrayEntrySlot (Nat.toB256 (done.length + 1))) = entry.1
        rw [hw.arrayWords done.length hdone, hsplit,
          targetAt_append_cons_length]
      have h32 : (32 : B256).toNat = 32 :=
        B256.toNat_toB256_of_lt (by norm_num)
      have hdone256 : done.length < 2 ^ 256 := by
        have hlength := hw.entries_length_le
        norm_num at hlength ⊢
        omega
      have hlength256 : entries.length < 2 ^ 256 := by
        have hlength := hw.entries_length_le
        norm_num at hlength ⊢
        omega
      have hltWord :
          Nat.toB256 done.length < Nat.toB256 entries.length := by
        apply B256.lt_of_toNat_lt_toNat
        rw [B256.toNat_toB256_of_lt hdone256,
          B256.toNat_toB256_of_lt hlength256]
        exact hdone
      have hltCheck :
          Nat.toB256 done.length <? Nat.toB256 entries.length = 1 := by
        simp [B256.ltCheck, hltWord]
      have hrestGas := enumLoopGasWarmFrom_ge (done.length + 1) rest
      func_run (16) [3, 1]
      all_goals try {
        simp only [Devm.gasLeft_setMach, enumLoopGasWarmFrom_cons]
        norm_num [gVerylow, gLow, gHigh, gJumpdest, gasWarmAccess]
        omega }
      all_goals try { rw [h32, enumPrefixMemory_extCost_length]; rfl }
      all_goals try {
        rw [h32, enumPrefixMemory_read_length_fst, B256.toB256_toBytes]
        exact hltCheck }
      have hmulcomm : (32 : B256) * Nat.toB256 done.length =
          Nat.toB256 done.length * 32 := by
        apply B256.toNat_inj
        rw [B256.toNat_mul, B256.toNat_mul,
          Nat.mul_comm (B256.toNat 32) (Nat.toB256 done.length).toNat]
      have hoffset : (64 : B256) + 32 * Nat.toB256 done.length =
          Nat.toB256 (64 + 32 * done.length) := by
        calc
          _ = Nat.toB256 done.length * 32 + 64 := by
            rw [B256.add_comm (xs := (64 : B256))
              (ys := (32 : B256) * Nat.toB256 done.length), hmulcomm]
          _ = Nat.toB256 (32 * done.length) + 64 := by
            rw [(hw.enumeration_word_arithmetic hdone).2.1]
          _ = _ := (hw.enumeration_word_arithmetic hdone).2.2
      have hoffsetNat :
          (Nat.toB256 (64 + 32 * done.length)).toNat =
            64 + 32 * done.length :=
        (hw.enumeration_offsets_toB256_toNat hdone).2.1
      have hcursor : (1 : B256) + Nat.toB256 done.length =
          Nat.toB256 (done.length + 1) := by
        rw [B256.add_comm (xs := (1 : B256))
          (ys := Nat.toB256 done.length),
          (hw.enumeration_word_arithmetic hdone).1]
      simp only [Devm.getStorVal_setMach, h32,
        enumPrefixMemory_read_length_snd, hvalue, hoffset]
      let delta :=
        calculateMemoryGasCost (64 + 32 * (done.length + 1)) -
          calculateMemoryGasCost (64 + 32 * done.length)
      have hmstore : Ninst.RunCompiled sevm
          (base.setMach
            ⟨[Nat.toB256 (64 + 32 * done.length), entry.1,
                Nat.toB256 done.length],
              enumPrefixMemory entries done,
              G + enumLoopGasWarmFrom done.length (entry :: rest) - 158⟩)
          Ninst.mstore
          (base.setMach
            ⟨[Nat.toB256 done.length],
              enumPrefixMemory entries (done ++ [entry]),
              G + enumLoopGasWarmFrom (done.length + 1) rest + 18⟩) := by
        refine Ninst.runCompiled_mstore_of (e := delta) rfl ?_ ?_ ?_
        · rw [hoffsetNat]
          exact enumPrefixMemory_extCost_next base
            [Nat.toB256 (64 + 32 * done.length), entry.1,
              Nat.toB256 done.length]
            entries done
            (G + enumLoopGasWarmFrom done.length (entry :: rest) - 158)
        · simp only [Devm.gasLeft_setMach, enumLoopGasWarmFrom_cons]
          norm_num [gVerylow, delta]
          omega
        · rw [Devm.memory_setMach, hoffsetNat]
          exact (enumPrefixMemory_append entries done entry).symm
      refine Func.RunCompiled.next hmstore ?_
      func_run (2) [Nat.toB256 (done.length + 1)]
      refine Func.runCompiled_call'
        (G := G + enumLoopGasWarmFrom (done.length + 1) rest)
        hfs (by simp only [Devm.stack_setMach, List.length_singleton]; omega)
        ?_ ?_
      · simp only [Devm.gasLeft_setMach]
        norm_num [gVerylow, gMid, gJumpdest]
        omega
      · have hsplit' : entries = (done ++ [entry]) ++ rest := by
          simpa [List.append_assoc] using hsplit
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, List.length_append, List.length_singleton,
          Nat.add_one] using ih (done ++ [entry]) hsplit'

private theorem enumFirstHeaderMemory_extCost_second
    (base : Devm) (stack : List B256) (G : Nat) :
    (base.setMach
      ⟨stack, Mem.empty.write 0 (Nat.toB256 32).toBytes, G⟩).extCost
      [⟨32, 32⟩] = 3 := by
  apply Devm.extCost_of_size
  · rw [Mem.size_write_word_at, if_neg (by simp [Mem.empty])]
  · rfl

/-- The public enumeration body initializes the ABI header and invokes the
recursive loop with exactly the finite warm budget derived above. -/
theorem getPausables_body_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (entries : List Entry)
    (G : Nat)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hwarm : ∀ key ∈ enumerationStorageKeys entries,
      (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys)
    (hfs : fs[enumLoopSlot]? = some enumLoop) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + getPausablesGasWarm entries⟩)
      getPausables
      ((base.setMach ⟨[], enumPrefixMemory entries entries, G⟩).withOutput
        (abiAddressArray entries)) := by
  unfold getPausables
  have hloopGas := enumLoopGasWarmFrom_ge 0 entries
  func_run (4) [3]
  all_goals try {
    simp only [Devm.gasLeft_setMach]
    norm_num [getPausablesGasWarm, gVerylow, gBase]
    omega }
  all_goals try { exact Devm.extCost_empty_word }
  refine Func.RunCompiled.next
    (Ninst.runCompiled_sload_warm
      (v := Nat.toB256 entries.length)
      (G := G + getPausablesGasWarm entries - 114)
      rfl ?_ ?_ ?_ (by simp)) ?_
  · exact hwarm arrayLengthSlot
      (arrayLengthSlot_mem_enumerationStorageKeys entries)
  · rw [Devm.getStorVal_setMach]
    change (logicalStorageOfStor
      (Devm.getStor base sevm.currentTarget)).read arrayLengthSlot =
        Nat.toB256 entries.length
    exact hw.lengthWord
  · simp only [Devm.gasLeft_setMach]
    norm_num [gasWarmAccess, getPausablesGasWarm]
    omega
  func_run (3) [3]
  all_goals try {
    simp only [Devm.gasLeft_setMach]
    norm_num [getPausablesGasWarm, gVerylow, gBase]
    omega }
  all_goals try {
    simp only [Devm.setMach_setMach, Devm.memory_setMach]
    exact enumFirstHeaderMemory_extCost_second _ _ _ }
  refine Func.runCompiled_call'
    (G := G + enumLoopGasWarmFrom 0 entries)
    hfs ?_ ?_ ?_
  · simp only [Devm.stack_setMach, List.length_singleton]
    omega
  · simp only [Devm.gasLeft_setMach]
    norm_num [getPausablesGasWarm, calculateMemoryGasCost, ceilDiv,
      gMemory, gVerylow, gMid, gJumpdest]
    omega
  · have hzeroOffset : ((0 : B256) * 32).toNat = 0 := by decide
    have honeOffset : ((1 : B256) * 32).toNat = 32 := by decide
    have hzeroWord : Nat.toB256 0 = (0 : B256) := by decide
    have h32Word : Nat.toB256 32 = (32 : B256) := by decide
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach, enumPrefixMemory, hzeroOffset, honeOffset,
      hzeroWord, h32Word, List.length_nil, List.foldl_nil] using
      enumLoop_runCompiled fs sevm base entries [] entries G
        (by simp) hw hwarm hfs

/-- Exact cost of the emitted runtime entry and well-formed selector path from
program counter zero to the `getPausables` body boundary. -/
def getPausablesDispatchGas : Nat := 130

def getPausablesRuntimeGas (entries : List Entry) : Nat :=
  getPausablesDispatchGas + getPausablesGasWarm entries

/-- Direct-runtime resources scale with the finite Registry witness and impose
no additional list-length cap. -/
structure EnumerationRuntimeResources (sevm : Sevm) (pre : Devm)
    (entries : List Entry) : Prop where
  stack_empty : pre.stack = []
  memory_empty : pre.memory = Mem.empty
  warm : ∀ key ∈ enumerationStorageKeys entries,
    (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ pre.accessedStorageKeys
  gas_sufficient : getPausablesRuntimeGas entries ≤ pre.gasLeft

def preparedEnumerationRuntimeState (sevm : Sevm) (base : Devm)
    (entries : List Entry) : Devm :=
  (prepareEnumerationStorage sevm base entries).setMach
    ⟨[], Mem.empty, getPausablesRuntimeGas entries⟩

theorem enumerationRuntimeResources_prepared (sevm : Sevm) (base : Devm)
    (entries : List Entry) :
    EnumerationRuntimeResources sevm
      (preparedEnumerationRuntimeState sevm base entries) entries := by
  refine ⟨rfl, rfl, ?_, Nat.le_refl _⟩
  intro key hkey
  exact prepareEnumerationStorage_warm sevm base entries hkey

/-- A well-formed direct `getPausables()` call through the exact parameterized
runtime reaches the verified body, returns the complete ordered ABI image, and
uses the concrete current target as both code and storage owner.  The code
hypothesis and compiler equality make the emitted-code boundary explicit. -/
theorem getPausables_runCompiled
    (dp : DeployParams) (sevm : Sevm) (base : Devm) (entries : List Entry)
    (G : Nat)
    (hdata : sevm.data.length.toB256 = 4)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "getPausables" [])
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hwarm : ∀ key ∈ enumerationStorageKeys entries,
      (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys) :
    Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + getPausablesDispatchGas + getPausablesGasWarm entries⟩)
        (runtime dp)
        ((base.setMach ⟨[], enumPrefixMemory entries entries, G⟩).withOutput
          (abiAddressArray entries)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  constructor
  · refine Prog.runCompiled_intro
      (mid := base.setMach ⟨[], Mem.empty,
        G + 129 + getPausablesGasWarm entries⟩)
      (G := G + 129 + getPausablesGasWarm entries) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, getPausablesDispatchGas, gJumpdest]
      omega
    · rfl
    · have hdataNonzero :
          B256.eqCheck sevm.data.length.toB256 4 = 1 := by
        simp [B256.eqCheck, hdata]
      have hvalueZero : B256.eqCheck sevm.value 0 = 1 := by
        simp [B256.eqCheck, hvalue]
      have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "getPausables" [] := hselector
      have htop : B256.gtCheck (selector "pause" [.address])
          (selector "getPausables" []) = 1 := by decide
      have hleft : B256.gtCheck (selector "getPauser" [.address])
          (selector "getPausables" []) = 0 := by decide
      have hfirst : B256.eqCheck (selector "getPauser" [.address])
          (selector "getPausables" []) = 0 := by decide
      have hleaf : B256.eqCheck (selector "getPausables" [])
          (selector "getPausables" []) = 1 := by decide
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (27) [0, 0, selector "getPausables" [], 1, 0, 0, 1]
      have hboundary :
          G + 129 + getPausablesGasWarm entries - 129 =
            G + getPausablesGasWarm entries := by omega
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
        runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
        List.take, List.drop, List.head?, Option.map, Option.getD,
        linearDispatchWith] using
        getPausables_body_runCompiled
          (runtimeMain dp :: aux) sevm base entries G
            hw hwarm (by rfl)
  · rw [hcode, lidoCircuitBreakerCode_compile]

/-- Sufficient runtime resources construct an exact successful public run;
the residual gas is the supplied gas minus the finite per-list cost. -/
theorem EnumerationRuntimeResources.getPausables_runCompiled
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {entries : List Entry}
    (resources : EnumerationRuntimeResources sevm pre entries)
    (hdata : sevm.data.length.toB256 = 4)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "getPausables" [])
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre sevm.currentTarget)) entries) :
    Prog.RunCompiled sevm pre (runtime dp)
        ((pre.setMach ⟨[], enumPrefixMemory entries entries,
          pre.gasLeft - getPausablesRuntimeGas entries⟩).withOutput
            (abiAddressArray entries)) ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have hgas :
      pre.gasLeft - getPausablesRuntimeGas entries +
          getPausablesDispatchGas + getPausablesGasWarm entries =
        pre.gasLeft := by
    rw [Nat.add_assoc, ← getPausablesRuntimeGas]
    exact Nat.sub_add_cancel resources.gas_sufficient
  have hpre : pre.setMach ⟨[], Mem.empty, pre.gasLeft⟩ = pre := by
    rw [← resources.stack_empty, ← resources.memory_empty]
    cases pre
    rfl
  simpa only [hgas, hpre] using
    Blanc.LidoCircuitBreaker.getPausables_runCompiled dp sevm pre entries
      (pre.gasLeft - getPausablesRuntimeGas entries)
      hdata hvalue hselector hcode hw resources.warm

theorem getPausables_post_worldEq (base : Devm) (entries : List Entry)
    (G : Nat) :
    Devm.WorldEq base
      ((base.setMach ⟨[], enumPrefixMemory entries entries, G⟩).withOutput
        (abiAddressArray entries)) := by
  exact ⟨rfl, rfl⟩

theorem getPausables_post_logs (base : Devm) (entries : List Entry)
    (G : Nat) :
    ((base.setMach ⟨[], enumPrefixMemory entries entries, G⟩).withOutput
      (abiAddressArray entries)).logs = base.logs := rfl

/-- The landed finite component certificate excludes every owned same-frame
SSTORE occurrence on every raw derivation below the exact public enumeration
source cursor.  This is deliberately an occurrence theorem, not a termination
or general effect-silence theorem. -/
theorem getPausables_noSstore_occurrence
    {root : Exec.Deriv} {path : Prog.SourcePath}
    (cursor : Exec.Deriv.SourceCursor root
      (runtime officialParams) path getPausables)
    (compiled :
      some root.sevm.code.toList = (runtime officialParams).compile)
    (occurrence : Exec.NinstOccurrence root)
    (owned : Exec.Deriv.ParentPrefix cursor.node occurrence.node) :
    occurrence.instruction ≠ .reg .sstore :=
  occurrence.instruction_ne_sstore_of_entrySstoreFree
    cursor compiled enumerationComponent enumeration_entry_sstore_free owned

theorem canonicalAddress_mask_zero {word : B256}
    (h : canonicalAddress word) : addressMask &&& word = 0 := by
  rw [← validAdr_iff]
  rcases word with ⟨⟨wz, wh⟩, wl⟩
  have hzNat : wz.toNat = 0 := by
    simp only [canonicalAddress, B256.toNat_eq, B128.toNat_eq] at h
    have hwh := UInt64.toNat_lt wh
    have hwl := B128.toNat_lt (x := wl)
    omega
  have hwhLt : wh.toNat < 2 ^ 32 := by
    simp only [canonicalAddress, B256.toNat_eq, B128.toNat_eq] at h
    have hwz := UInt64.toNat_lt wz
    have hwl := B128.toNat_lt (x := wl)
    omega
  have hz : wz = 0 := by
    apply UInt64.toNat_inj.mp
    simpa using hzNat
  have hwh : wh.toUInt32.toUInt64 = wh := by
    apply UInt64.toNat_inj.mp
    simp only [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    rw [Nat.mod_eq_of_lt hwhLt]
  exact ⟨⟨wh.toUInt32, wl⟩, by simp [Adr.toB256, hz, hwh]⟩

def registryScalarBodyGasWarm : Nat := 179

private theorem registryScalarReturn_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (word : B256) (G : Nat) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[0, 32], Mem.empty.write 0 word.toBytes, G⟩)
        Func.ret post ∧
      Devm.output post = word.toBytes := by
  let retPre := base.setMach
    ⟨[0, 32], Mem.empty.write 0 word.toBytes, G⟩
  let d := (retPre.setMach ⟨[], retPre.memory, G⟩).memRead 0 32
  let post := d.2.withOutput word.toBytes
  refine ⟨post, ?_, rfl⟩
  have hread :
      (retPre.setMach ⟨[], retPre.memory, G⟩).memRead 0 32 =
        ⟨word.toBytes, d.2⟩ := by
    exact Prod.ext
      (Devm.memRead_word_fst
        (by simp only [retPre, Devm.memory_setMach]))
      rfl
  exact Func.runCompiled_ret_of (devm := retPre) (G := G) (e := 0)
    (out := word.toBytes) (d' := d.2) rfl
    (Devm.extCost_word_word Mem.size_write_word) rfl hread

/-- Exact compiled-body result for the assignment view on a canonical ABI
address word and the same concrete Registry owner used by enumeration. -/
theorem getPauser_body_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (entries : List Entry)
    (target : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hword : Sevm.dataWord sevm 4 = target)
    (htarget : canonicalAddress target)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hwarm : (⟨sevm.currentTarget, assignmentSlot target⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, G + registryScalarBodyGasWarm⟩)
        getPauser post ∧
      Devm.output post = (assignmentAt entries target).toBytes := by
  have hcanonical := canonicalAddress_mask_zero htarget
  have hstorage :
      Devm.getStorVal base sevm.currentTarget (assignmentSlot target) =
        assignmentAt entries target := by
    change (logicalStorageOfStor
      (Devm.getStor base sevm.currentTarget)).read (assignmentSlot target) =
        assignmentAt entries target
    exact hw.assignments target htarget
  unfold getPauser requireStaticArgs canonicalAddressArg arg cdl
    checkNonAddress pushAddressMask tagTop returnWord mstoreAt
    returnMemoryRange pushList registryScalarBodyGasWarm
  have hword0 : Sevm.dataWord sevm (32 * 0 + 4) = target := by
    exact hword
  have hgasFinal : G + 179 - 179 = G := by omega
  rcases registryScalarReturn_runCompiled fs sevm base
      (assignmentAt entries target) G with ⟨post, hreturn, houtput⟩
  refine ⟨post, ?_, houtput⟩
  func_run [0, ~~~(0 : B256), addressMask, 0, assignmentSlot target, 3]
  all_goals try { rw [hword0]; exact hcanonical }
  all_goals try { rw [hword0]; rfl }
  all_goals try {
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word }
  all_goals try {
    rw [show ((0 : B256) * 32).toNat = 0 by decide,
      Devm.getStorVal_setMach, hstorage, hgasFinal]
    exact hreturn }

/-- Exact compiled-body result for the per-pauser multiplicity view on a
canonical ABI address word and the same concrete Registry owner. -/
theorem getPausableCount_body_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm) (entries : List Entry)
    (pauser : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base sevm.currentTarget)) entries)
    (hwarm : (⟨sevm.currentTarget, countSlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, G + registryScalarBodyGasWarm⟩)
        getPausableCount post ∧
      Devm.output post =
        (Nat.toB256 (assignmentCount entries pauser)).toBytes := by
  have hcanonical := canonicalAddress_mask_zero hpauser
  have hstorage :
      Devm.getStorVal base sevm.currentTarget (countSlot pauser) =
        Nat.toB256 (assignmentCount entries pauser) := by
    change (logicalStorageOfStor
      (Devm.getStor base sevm.currentTarget)).read (countSlot pauser) =
        Nat.toB256 (assignmentCount entries pauser)
    exact hw.counts pauser hpauser
  unfold getPausableCount requireStaticArgs canonicalAddressArg arg cdl
    checkNonAddress pushAddressMask tagTop returnWord mstoreAt
    returnMemoryRange pushList registryScalarBodyGasWarm
  have hword0 : Sevm.dataWord sevm (32 * 0 + 4) = pauser := by
    exact hword
  have hgasFinal : G + 179 - 179 = G := by omega
  rcases registryScalarReturn_runCompiled fs sevm base
      (Nat.toB256 (assignmentCount entries pauser)) G with
    ⟨post, hreturn, houtput⟩
  refine ⟨post, ?_, houtput⟩
  func_run [0, ~~~(0 : B256), addressMask, 0, countSlot pauser, 3]
  all_goals try { rw [hword0]; exact hcanonical }
  all_goals try { rw [hword0]; rfl }
  all_goals try {
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word }
  all_goals try {
    rw [show ((0 : B256) * 32).toNat = 0 by decide,
      Devm.getStorVal_setMach, hstorage, hgasFinal]
    exact hreturn }

theorem assignmentCount_eq_multiplicity (entries : List Entry)
    (pauser : B256) :
    assignmentCount entries pauser =
      (entries.map Prod.snd).count pauser := by
  induction entries with
  | nil => simp [assignmentCount]
  | cons entry rest ih =>
      simp only [assignmentCount, List.map_cons, List.count_cons]
      rw [ih]
      by_cases h : entry.2 = pauser
      · simp [h, Nat.add_comm]
      · simp [h]

/-- Model-level consequences shared by the three exact Registry view runs. -/
structure RegistrySnapshotCoherence (entries : List Entry)
    (target pauser : B256) : Prop where
  assignment_iff_member :
    assignmentAt entries target ≠ 0 ↔ target ∈ entries.map Prod.fst
  returned_nonzero_canonical :
    ∀ entry ∈ entries, entry.1 ≠ 0 ∧ canonicalAddress entry.1
  returned_targets_nodup : (entries.map Prod.fst).Nodup
  count_eq_multiplicity :
    assignmentCount entries pauser = (entries.map Prod.snd).count pauser
  zero_count : assignmentCount entries 0 = 0

/-- Every stable concrete Registry witness induces the model-facing coherence
facts used by the exact three-view family. -/
theorem RegistryWitness.snapshotCoherence
    {base : Devm} {ca : Adr} {entries : List Entry}
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor base ca)) entries)
    (target pauser : B256) (htarget : canonicalAddress target) :
    RegistrySnapshotCoherence entries target pauser := by
  have hassignment :
      (Devm.getStor base ca).get (assignmentSlot target) =
        assignmentAt entries target := by
    simpa only [logicalStorageOfStor] using hw.assignments target htarget
  have hmember :=
    (membershipEquivalence_registerPauser
      (post := base) (ca := ca) hw htarget).1
  rw [hassignment] at hmember
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    rw [B256.toNat_zero]
    norm_num
  have hzeroWord : Nat.toB256 (assignmentCount entries 0) = 0 := by
    have hcount := hw.counts 0 hzeroCanonical
    exact hcount.symm.trans hw.zeroCount
  have hzeroCount : assignmentCount entries 0 = 0 := by
    have hnat := congrArg B256.toNat hzeroWord
    rw [B256.toNat_toB256_of_lt (hw.assignmentCount_lt_2pow256 0),
      B256.toNat_zero] at hnat
    exact hnat
  exact ⟨hmember, hw.targetsValid, hw.targetsNodup,
    assignmentCount_eq_multiplicity entries pauser, hzeroCount⟩

/-- The exact enumeration, assignment, and multiplicity bodies read one
concrete Registry snapshot.  Their successful outputs therefore agree with
ordered membership, target validity/uniqueness, and pauser multiplicity. -/
theorem registryViews_coherent
    (fs : List Func) (enumSevm pauserSevm countSevm : Sevm)
    (base : Devm) (entries : List Entry) (target pauser : B256)
    (enumG pauserG countG : Nat)
    (hpauserOwner : pauserSevm.currentTarget = enumSevm.currentTarget)
    (hcountOwner : countSevm.currentTarget = enumSevm.currentTarget)
    (hpauserData : pauserSevm.data.length.toB256 <? 36 = 0)
    (hpauserWord : Sevm.dataWord pauserSevm 4 = target)
    (hcountData : countSevm.data.length.toB256 <? 36 = 0)
    (hcountWord : Sevm.dataWord countSevm 4 = pauser)
    (htarget : canonicalAddress target)
    (hpauser : canonicalAddress pauser)
    (hw : RegistryWitness
      (logicalStorageOfStor
        (Devm.getStor base enumSevm.currentTarget)) entries)
    (henumWarm : ∀ key ∈ enumerationStorageKeys entries,
      (⟨enumSevm.currentTarget, key⟩ : Adr × B256) ∈
        base.accessedStorageKeys)
    (hpauserWarm :
      (⟨pauserSevm.currentTarget, assignmentSlot target⟩ : Adr × B256) ∈
        base.accessedStorageKeys)
    (hcountWarm :
      (⟨countSevm.currentTarget, countSlot pauser⟩ : Adr × B256) ∈
        base.accessedStorageKeys)
    (hfs : fs[enumLoopSlot]? = some enumLoop) :
    ∃ pauserPost countPost,
      Func.RunCompiled fs enumSevm
        (base.setMach ⟨[], Mem.empty,
          enumG + getPausablesGasWarm entries⟩)
        getPausables
        ((base.setMach ⟨[], enumPrefixMemory entries entries, enumG⟩).withOutput
          (abiAddressArray entries)) ∧
      Func.RunCompiled fs pauserSevm
        (base.setMach ⟨[], Mem.empty,
          pauserG + registryScalarBodyGasWarm⟩)
        getPauser pauserPost ∧
      Devm.output pauserPost = (assignmentAt entries target).toBytes ∧
      Func.RunCompiled fs countSevm
        (base.setMach ⟨[], Mem.empty,
          countG + registryScalarBodyGasWarm⟩)
        getPausableCount countPost ∧
      Devm.output countPost =
        (Nat.toB256 (assignmentCount entries pauser)).toBytes ∧
      RegistrySnapshotCoherence entries target pauser := by
  have hwPauser : RegistryWitness
      (logicalStorageOfStor
        (Devm.getStor base pauserSevm.currentTarget)) entries := by
    simpa only [hpauserOwner] using hw
  have hwCount : RegistryWitness
      (logicalStorageOfStor
        (Devm.getStor base countSevm.currentTarget)) entries := by
    simpa only [hcountOwner] using hw
  rcases getPauser_body_runCompiled fs pauserSevm base entries target pauserG
      hpauserData hpauserWord htarget hwPauser hpauserWarm with
    ⟨pauserPost, hpauserRun, hpauserOutput⟩
  rcases getPausableCount_body_runCompiled fs countSevm base entries
      pauser countG hcountData hcountWord hpauser hwCount hcountWarm with
    ⟨countPost, hcountRun, hcountOutput⟩
  refine ⟨pauserPost, countPost,
    getPausables_body_runCompiled fs enumSevm base entries enumG
      hw henumWarm hfs,
    hpauserRun, hpauserOutput, hcountRun, hcountOutput, ?_⟩
  have hassignment :
      (Devm.getStor base enumSevm.currentTarget).get (assignmentSlot target) =
        assignmentAt entries target := by
    simpa only [logicalStorageOfStor] using hw.assignments target htarget
  have hmember :=
    (membershipEquivalence_registerPauser
      (post := base) (ca := enumSevm.currentTarget) hw htarget).1
  rw [hassignment] at hmember
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    rw [B256.toNat_zero]
    norm_num
  have hzeroWord : Nat.toB256 (assignmentCount entries 0) = 0 := by
    have hcount := hw.counts 0 hzeroCanonical
    exact hcount.symm.trans hw.zeroCount
  have hzeroCount : assignmentCount entries 0 = 0 := by
    have hnat := congrArg B256.toNat hzeroWord
    rw [B256.toNat_toB256_of_lt (hw.assignmentCount_lt_2pow256 0),
      B256.toNat_zero] at hnat
    exact hnat
  exact ⟨hmember, hw.targetsValid, hw.targetsNodup,
    assignmentCount_eq_multiplicity entries pauser, hzeroCount⟩

private theorem of_logWith300_val {e : Sevm} {s s' : Devm}
    {ev a b c : B256} {xs : Stack}
    (hp : ev :: a :: b :: c :: xs <<+ s.stack)
    (h : Line.Run e s (logWith 3 0 0) s') :
    xs <<+ s'.stack ∧
      s'.logs = s.logs ++ [⟨e.currentTarget, [ev, a, b, c], []⟩] := by
  rcases Line.of_run_cons h with ⟨s₁, hzero₁, hrest₁⟩
  rcases Line.of_run_cons hrest₁ with ⟨s₂, hzero₂, hrest₂⟩
  rcases Line.of_run_cons hrest₂ with ⟨s₃, hlog, hnil⟩
  cases hnil
  have hz₁ := of_run_pushB256 hzero₁
  have hz₂ := of_run_pushB256 hzero₂
  have hzeroWord : (0 * 32 : B256) = 0 := rfl
  rw [hzeroWord] at hz₁ hz₂
  have hp₁ : (0 : B256) :: ev :: a :: b :: c :: xs <<+ s₁.stack := by
    simpa using prefix_of_push hz₁ hp
  have hp₂ : (0 : B256) :: 0 :: ev :: a :: b :: c :: xs <<+ s₂.stack := by
    simpa using prefix_of_push hz₂ hp₁
  rcases of_run_log_val hlog with
    ⟨mi, sz, topics, hlen, hpop, hlogs⟩
  have hknown : ([0, 0, ev, a, b, c] : List B256) <<+ s₂.stack := by
    exact @pref_trans _ [0, 0, ev, a, b, c]
      ([0, 0, ev, a, b, c] ++ xs) _ ⟨xs, rfl⟩ (by simpa using hp₂)
  have heq : ([0, 0, ev, a, b, c] : List B256) =
      mi :: sz :: topics :=
    List.pref_unique (by simp [hlen]) hknown (pref_of_split hpop)
  simp only [List.cons.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  constructor
  · exact of_append_pref hpop (by simpa using hp₂)
  · rw [hlogs, ← hz₂.logs, ← hz₁.logs, ← hz₂.memory, ← hz₁.memory]
    rfl

private theorem enumeration_prefix_of_loadWord_image
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {img : Bytes} {word value : B256}
    (hp : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hvalue : Bytes.toB256
      (img.sliceD (word * 32).toNat 32 0) = value)
    (run : Line.Run sevm pre (loadWord word) post) :
    value :: xs <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory img ∧
      Devm.getStor pre = Devm.getStor post ∧
      pre.logs = post.logs := by
  unfold loadWord at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hb1 := of_run_pushB256 q1
  have hp1 : (word * 32) :: xs <<+ s1.stack :=
    prefix_of_push hb1 hp
  have hr1 : Mem.Reads s1.memory img := by
    rw [← hb1.memory]
    exact hr
  have hwf1 : Mem.Wf s1.memory := by
    rw [← hb1.memory]
    exact hwf
  rcases Line.of_run_cons run with ⟨s2, q2, hnil⟩
  cases hnil
  rcases prefix_of_mload_val q2 hp1 hr1 with ⟨hp2, hm2, _⟩
  rw [hvalue] at hp2
  refine ⟨hp2, ?_, ?_, ?_, ?_⟩
  · rw [hm2]
    exact hwf1.extend _ _
  · rw [hm2]
    exact Mem.Reads.extend hr1 _ _
  · exact Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2 Line.Run.nil))
  · rcases of_run_reg q2 with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore] at run
    rcases Except.bind_eq_ok run with ⟨⟨si, t1⟩, h1, run1⟩
    rcases Except.bind_eq_ok run1 with ⟨t2, h2, run2⟩
    rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
    have hb := Devm.burn_of_chargeGas h2
    have hpush := Devm.push_of_push run2
    exact hb1.logs.trans (((p1.logs.trans hb.logs).trans rfl).trans hpush.logs)

/-- Every successful source execution through the sole production event site
reaches a post-log continuation state with exactly one appended `PauserSet`
record and unchanged Registry storage. -/
theorem finishSetPauser_run_extracts_event
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {newPauser previousPauser target : B256}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hrun : Func.Run fs sevm pre finishSetPauser final) :
    ∃ logged,
      logged.logs = pre.logs ++
        [⟨sevm.currentTarget,
          [pauserSetEvent, target, previousPauser, newPauser], []⟩] ∧
      Devm.getStor logged = Devm.getStor pre ∧
      Func.Run fs sevm logged
        (loadWord continuationWord +++ Ninst.iszero :::
          (Func.call pauseAfterSetSlot).branch
            (Func.call registerAfterSetSlot)) final := by
  simp only [finishSetPauser] at hrun
  rcases of_run_prepend (loadWord newPauserWord) _ hrun with
    ⟨sNew, hloadNew, h₁⟩
  rcases of_run_prepend (loadWord previousPauserWord) _ h₁ with
    ⟨sPrevious, hloadPrevious, h₂⟩
  rcases of_run_prepend (loadWord targetWord) _ h₂ with
    ⟨sTarget, hloadTarget, h₃⟩
  rcases of_run_next h₃ with ⟨sEvent, hpushEvent, h₄⟩
  rcases of_run_prepend (logWith 3 0 0) _ h₄ with
    ⟨sLog, hlog, htail⟩
  have hp₀ : pre.stack <<+ pre.stack := by
    simpa only [List.append_nil] using pref_append pre.stack []
  rcases enumeration_prefix_of_loadWord_image hp₀ hwf hr hnewRead hloadNew with
    ⟨hpNew, hwfNew, hrNew, hstorNew, hlogsNew⟩
  rcases enumeration_prefix_of_loadWord_image
      hpNew hwfNew hrNew hpreviousRead hloadPrevious with
    ⟨hpPrevious, hwfPrevious, hrPrevious, hstorPrevious, hlogsPrevious⟩
  rcases enumeration_prefix_of_loadWord_image
      hpPrevious hwfPrevious hrPrevious htargetRead hloadTarget with
    ⟨hpTarget, _, _, hstorTarget, hlogsTarget⟩
  have hpush := of_run_pushB256 hpushEvent
  have hpEvent :
      pauserSetEvent :: target :: previousPauser :: newPauser :: pre.stack
        <<+ sEvent.stack :=
    prefix_of_push hpush hpTarget
  have hlogResult := of_logWith300_val hpEvent hlog
  have hlogsEvent : sTarget.logs = sEvent.logs := hpush.logs
  have hlogs : sLog.logs = pre.logs ++
      [⟨sevm.currentTarget,
        [pauserSetEvent, target, previousPauser, newPauser], []⟩] := by
    rw [hlogResult.2, ← hlogsEvent, ← hlogsTarget,
      ← hlogsPrevious, ← hlogsNew]
  have hstorEvent : Devm.getStor sTarget = Devm.getStor sEvent :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushEvent
  have hstorLog : Devm.getStor sEvent = Devm.getStor sLog :=
    Line.of_inv Devm.getStor (by line_inv) hlog
  exact ⟨sLog, hlogs,
    (hstorNew.trans (hstorPrevious.trans
      (hstorTarget.trans (hstorEvent.trans hstorLog)))).symm,
    htail⟩

set_option maxRecDepth 4096 in
/-- An exact successful emitted-kernel execution exposes the stable S2
Registry poststate before appending the sole production `PauserSet` log, then
selects exactly the saved register or pre-yield pause continuation. -/
theorem pauserSet_local_transition
    (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target newPauser continuation : B256}
    (howner : sevm.currentTarget = ca)
    (hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htarget : canonicalAddress target)
    (hnew : canonicalAddress newPauser)
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    ∃ trace postRegistry postImg logged,
      setPauserSourceTrace entries target newPauser = some trace ∧
      setPauser entries target newPauser = some trace.postEntries ∧
      Devm.getStor postRegistry ca =
        applyRegistryWrites (Devm.getStor pre ca) trace.writes ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor postRegistry ca))
        trace.postEntries ∧
      logged.logs = postRegistry.logs ++
        [⟨ca,
          [pauserSetEvent, target, assignmentAt entries target, newPauser],
          []⟩] ∧
      Devm.getStor logged = Devm.getStor postRegistry ∧
      Func.Run ((runtime dp).main :: (runtime dp).aux) sevm logged
        (loadWord continuationWord +++ Ninst.iszero :::
          (Func.call pauseAfterSetSlot).branch
            (Func.call registerAfterSetSlot)) final ∧
      ((continuation = 0 ∧
          ∃ registerPre,
            postRegistry.stack <<+ registerPre.stack ∧
            Mem.Wf registerPre.memory ∧
            Mem.Reads registerPre.memory postImg ∧
            Devm.getStor registerPre sevm.currentTarget =
              Devm.getStor postRegistry ca ∧
            Func.Run ((runtime dp).main :: (runtime dp).aux)
              sevm registerPre registerAfterSet final) ∨
        (continuation ≠ 0 ∧
          ∃ pausePre,
            postRegistry.stack <<+ pausePre.stack ∧
            Mem.Wf pausePre.memory ∧
            Mem.Reads pausePre.memory postImg ∧
            Devm.getStor pausePre sevm.currentTarget =
              Devm.getStor postRegistry ca ∧
            Func.Run ((runtime dp).main :: (runtime dp).aux)
              sevm pausePre pauseAfterSet final)) := by
  rcases setPauserKernel_exec_extracts_sourceTrace dp howner hcodeAddress
      hbytes htable hwf hr htargetRead hnewRead hcontinuationRead
      hw htarget hnew hexec with
    ⟨trace, postRegistry, postImg, htrace, hwfPost, hrPost,
      htargetPost, hnewPost, hpreviousPost, hcontinuationPost,
      hstorPost, hwPost, hfinish⟩
  have htarget0 : target ≠ 0 := by
    intro hzero
    rw [hzero, setPauserSourceTrace_target_zero] at htrace
    cases htrace
  have hmodel := (setPauser_sourceTrace_refines_model htarget0 htrace).1
  rcases finishSetPauser_run_extracts_event hwfPost hrPost
      hnewPost hpreviousPost htargetPost hfinish with
    ⟨logged, hlogs, hstorLogged, htail⟩
  rcases runtime_caller_lookups dp with
    ⟨hregisterLookup, hpauseLookup, panicData, hpanicLookup⟩
  have hsplit := finishSetPauser_run_split_continuation hwfPost hrPost
    hnewPost hpreviousPost htargetPost hcontinuationPost howner
    hregisterLookup hpauseLookup hfinish
  refine ⟨trace, postRegistry, postImg, logged, htrace, hmodel, hstorPost,
    hwPost, ?_, hstorLogged, htail, ?_⟩
  · simpa [howner] using hlogs
  · exact hsplit

/-- A target-zero entry cannot be an exact successful emitted-kernel
execution, hence it cannot reach the production event suffix.  The matching
forward error construction is `setPauser_zero_runCompiledTo_pausableZero_noRegistryWrite`. -/
theorem pauserSet_target_zero_no_success
    (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {newPauser continuation : B256}
    (howner : sevm.currentTarget = ca)
    (hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = 0)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hnew : canonicalAddress newPauser)
    (hexec : Exec (loc + 1) sevm pre (.ok final)) : False := by
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  rcases setPauserKernel_exec_extracts_sourceTrace dp howner hcodeAddress
      hbytes htable hwf hr htargetRead hnewRead hcontinuationRead
      hw hzeroCanonical hnew hexec with
    ⟨trace, postRegistry, postImg, htrace, rest⟩
  rw [setPauserSourceTrace_target_zero] at htrace
  cases htrace

/-- At the top-level message boundary an exact direct register or pause call
that settles with an error exposes no logs, so a raw frame-local `PauserSet`
record is not observable. -/
theorem pauserSet_settled_error_not_observable
    (dp : DeployParams) {msg : Msg} {state : State} {out : MsgCallOutput}
    {ca : Adr} {target newPauser : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = registerPauserCalldata target newPauser ∨
      msg.data = pauseCalldata target)
    (hrun : processMessageCall msg = .ok (state, out))
    (herror : out.error.isSome) : out.logs = [] :=
  processMessageCall_error_logs_eq_nil hrun herror

set_option maxRecDepth 4096 in
/-- A monitor observation derived from this exact successful local site agrees
with the stable post-Registry snapshot: the event records the pre-assignment
and requested pauser, while the poststate satisfies the same coherence facts
that the three exact Registry views expose.  This is deliberately local and
does not assert delivery, history completeness, or finality. -/
theorem registryObservation_sound
    (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target newPauser continuation : B256}
    (howner : sevm.currentTarget = ca)
    (hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htarget : canonicalAddress target)
    (hnew : canonicalAddress newPauser)
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    ∃ (trace : SetPauserSourceTrace) (postRegistry logged : Devm),
      setPauser entries target newPauser = some trace.postEntries ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor postRegistry ca))
        trace.postEntries ∧
      logged.logs = postRegistry.logs ++
        [⟨ca,
          [pauserSetEvent, target, assignmentAt entries target, newPauser],
          []⟩] ∧
      Devm.getStor logged = Devm.getStor postRegistry ∧
      RegistrySnapshotCoherence trace.postEntries target newPauser := by
  rcases pauserSet_local_transition dp howner hcodeAddress hbytes htable
      hwf hr htargetRead hnewRead hcontinuationRead hw htarget hnew hexec with
    ⟨trace, postRegistry, postImg, logged, htrace, hmodel, hstorPost,
      hwPost, hlogs, hstorLogged, htail, hsplit⟩
  exact ⟨trace, postRegistry, logged, hmodel, hwPost, hlogs,
    hstorLogged, hwPost.snapshotCoherence target newPauser htarget⟩

set_option maxRecDepth 1000

end Blanc.LidoCircuitBreaker
