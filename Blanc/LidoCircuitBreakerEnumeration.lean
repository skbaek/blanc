import Blanc.LidoCircuitBreakerRegistry

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

end Blanc.LidoCircuitBreaker
