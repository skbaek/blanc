import Blanc.LidoCircuitBreakerRegistry
import Blanc.Lift.MapSlot
import Blanc.AddressSlotProofs

/-! The deployed Lido Registry's Solidity storage layout, projected onto the
CircuitBreaker's existing tagged logical observation.  This is a storage
interpretation, not a bytecode execution claim. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc.LidoCircuitBreaker

/-- Solidity's dynamic address-array data base is the hash of its length slot. -/
def registryArrayBase : B256 := (5 : B256).toBytes.keccak

/-- Zero-based raw slot of an address in the deployed dynamic array. -/
def registryArraySlot (index : Nat) : B256 :=
  registryArrayBase + Nat.toB256 index

/-- Decode a tagged logical Registry key into the actual Solidity storage
families.  The arbitrary default outside those families is unobservable by a
`RegistryWitness`.  Address-typed fields discard raw high 96 bits. -/
def solRegistryStorage (raw : Stor) : LogicalStorage :=
  { read := fun key =>
      let region := key.toNat / 2 ^ 252
      let payload := Nat.toB256 (key.toNat % 2 ^ 252)
      if region = assignmentRegion then
        addressSlotReadWord (raw.get (mapSlot payload 3))
      else if region = indexRegion then
        raw.get (mapSlot payload 4)
      else if region = countRegion then
        raw.get (mapSlot payload 6)
      else if region = arrayRegion then
        if payload = 0 then raw.get 5
        else addressSlotReadWord
          (raw.get (registryArrayBase + (payload - 1)))
      else 0 }

private theorem tagged_region_payload
    {region : Nat} {payload : B256}
    (hregion : region < 16) (hpayload : payload.toNat < 2 ^ 252) :
    (slot region payload).toNat / 2 ^ 252 = region ∧
    Nat.toB256 ((slot region payload).toNat % 2 ^ 252) = payload := by
  have hslot : slot region payload = TaggedStorage.encode region payload := by
    rw [TaggedStorage.encode_eq_of_payload_lt hpayload]
    rfl
  rw [hslot]
  exact TaggedStorage.encode_region_payload_of_bounds hregion hpayload

theorem solRegistryStorage_assignment (raw : Stor) (target : B256)
    (hcanonical : canonicalAddress target) :
    (solRegistryStorage raw).read (assignmentSlot target) =
      addressSlotReadWord (raw.get (mapSlot target 3)) := by
  have h := tagged_region_payload (region := assignmentRegion)
    (by norm_num [assignmentRegion]) (canonicalAddress_payload_lt hcanonical)
  simp only [assignmentSlot, solRegistryStorage, h.1, h.2]
  simp

theorem solRegistryStorage_index (raw : Stor) (target : B256)
    (hcanonical : canonicalAddress target) :
    (solRegistryStorage raw).read (indexSlot target) =
      raw.get (mapSlot target 4) := by
  have h := tagged_region_payload (region := indexRegion)
    (by norm_num [indexRegion]) (canonicalAddress_payload_lt hcanonical)
  simp only [indexSlot, solRegistryStorage, h.1, h.2]
  simp [assignmentRegion, indexRegion]

theorem solRegistryStorage_count (raw : Stor) (pauser : B256)
    (hcanonical : canonicalAddress pauser) :
    (solRegistryStorage raw).read (countSlot pauser) =
      raw.get (mapSlot pauser 6) := by
  have h := tagged_region_payload (region := countRegion)
    (by norm_num [countRegion]) (canonicalAddress_payload_lt hcanonical)
  simp only [countSlot, solRegistryStorage, h.1, h.2]
  simp [assignmentRegion, indexRegion, countRegion]

theorem solRegistryStorage_length (raw : Stor) :
    (solRegistryStorage raw).read arrayLengthSlot = raw.get 5 := by
  have h := tagged_region_payload (region := arrayRegion) (payload := 0)
    (by norm_num [arrayRegion]) (by
      change (0 : Nat) < 2 ^ 252
      norm_num)
  simp only [arrayLengthSlot, solRegistryStorage, h.1, h.2]
  simp [assignmentRegion, indexRegion, countRegion, arrayRegion]

theorem solRegistryStorage_array (raw : Stor) (index : Nat)
    (hindex : index + 1 < 2 ^ 252) :
    (solRegistryStorage raw).read
      (arrayEntrySlot (Nat.toB256 (index + 1))) =
      addressSlotReadWord (raw.get (registryArraySlot index)) := by
  have h256 : index + 1 < 2 ^ 256 := by omega
  have hword : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt h256]
    exact hindex
  have h := tagged_region_payload (region := arrayRegion)
    (by norm_num [arrayRegion]) hword
  simp only [arrayEntrySlot, solRegistryStorage, h.1, h.2]
  have hnonzero : Nat.toB256 (index + 1) ≠ 0 := by
    intro heq
    have hn := congrArg B256.toNat heq
    rw [B256.toNat_toB256_of_lt h256] at hn
    change index + 1 = 0 at hn
    omega
  have hpred : Nat.toB256 (index + 1) - 1 = Nat.toB256 index := by
    simpa using (natToB256_pred_eq_sub_one (index + 1) (by omega) h256).symm
  simp [assignmentRegion, indexRegion, countRegion, arrayRegion,
    hnonzero, hpred, registryArraySlot]

/-! ## A single collision-freedom premise for every raw-write transport

`solKey` inverts `solRegistryStorage`'s decode: it is the actual Solidity
slot a tagged logical Registry key reads from.  `RegistryKeysFaithful`
replaces what would otherwise be one bespoke key-correspondence bundle per
transition (a `LocalRemovalKeys`, and a `LocalFreshKeys`/nonzero/absent-zero
copy of it) with one reviewable assumption: no other *observed* logical key
shares a raw slot with a *written* key.  This is never global Keccak
injectivity — only collision-freedom at the finitely many keys a
transition's writes and a witness's reads actually touch. -/

/-- Raw Solidity slot of a tagged logical Registry key, mirroring
`solRegistryStorage`'s decoding exactly. -/
def solKey (key : B256) : B256 :=
  let region := key.toNat / 2 ^ 252
  let payload := Nat.toB256 (key.toNat % 2 ^ 252)
  if region = assignmentRegion then mapSlot payload 3
  else if region = indexRegion then mapSlot payload 4
  else if region = countRegion then mapSlot payload 6
  else if region = arrayRegion then
    if payload = 0 then 5 else registryArrayBase + (payload - 1)
  else 0

theorem solKey_assignmentSlot {probe : B256} (h : canonicalAddress probe) :
    solKey (assignmentSlot probe) = mapSlot probe 3 := by
  have h' := tagged_region_payload (region := assignmentRegion)
    (by norm_num [assignmentRegion]) (canonicalAddress_payload_lt h)
  simp only [assignmentSlot, solKey, h'.1, h'.2]
  simp

theorem solKey_indexSlot {probe : B256} (h : canonicalAddress probe) :
    solKey (indexSlot probe) = mapSlot probe 4 := by
  have h' := tagged_region_payload (region := indexRegion)
    (by norm_num [indexRegion]) (canonicalAddress_payload_lt h)
  simp only [indexSlot, solKey, h'.1, h'.2]
  simp [assignmentRegion, indexRegion]

theorem solKey_countSlot {probe : B256} (h : canonicalAddress probe) :
    solKey (countSlot probe) = mapSlot probe 6 := by
  have h' := tagged_region_payload (region := countRegion)
    (by norm_num [countRegion]) (canonicalAddress_payload_lt h)
  simp only [countSlot, solKey, h'.1, h'.2]
  simp [assignmentRegion, indexRegion, countRegion]

theorem solKey_arrayLengthSlot : solKey arrayLengthSlot = 5 := by
  have h' := tagged_region_payload (region := arrayRegion) (payload := 0)
    (by norm_num [arrayRegion]) (by
      change (0 : Nat) < 2 ^ 252
      norm_num)
  simp only [arrayLengthSlot, solKey, h'.1, h'.2]
  simp [assignmentRegion, indexRegion, countRegion, arrayRegion]

theorem solKey_arrayEntrySlot {index : Nat} (hindex : index + 1 < 2 ^ 252) :
    solKey (arrayEntrySlot (Nat.toB256 (index + 1))) = registryArraySlot index := by
  have h256 : index + 1 < 2 ^ 256 := by omega
  have hword : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt h256]
    exact hindex
  have h' := tagged_region_payload (region := arrayRegion)
    (by norm_num [arrayRegion]) hword
  simp only [arrayEntrySlot, solKey, h'.1, h'.2]
  have hnonzero : Nat.toB256 (index + 1) ≠ 0 := by
    intro heq
    have hn := congrArg B256.toNat heq
    rw [B256.toNat_toB256_of_lt h256] at hn
    change index + 1 = 0 at hn
    omega
  have hpred : Nat.toB256 (index + 1) - 1 = Nat.toB256 index := by
    simpa using (natToB256_pred_eq_sub_one (index + 1) (by omega) h256).symm
  simp [assignmentRegion, indexRegion, countRegion, arrayRegion,
    hnonzero, hpred, registryArraySlot]

/-- The logical keys a `RegistryWitness` observes: canonical-address
payloads for the three mapping families, and array payloads `0 .. bound`
(the length slot, plus every populated entry slot).  `bound` is a plain
`Nat` rather than a specific `entries.length` so the same predicate covers
both a witness's *before* observation and the extra index a fresh write
introduces (its caller supplies whichever bound dominates both). -/
def RegistryObservable (bound : Nat) (key : B256) : Prop :=
  (∃ probe, canonicalAddress probe ∧ key = assignmentSlot probe) ∨
  (∃ probe, canonicalAddress probe ∧ key = indexSlot probe) ∨
  (∃ probe, canonicalAddress probe ∧ key = countSlot probe) ∨
  key = arrayLengthSlot ∨
  (∃ i, i < bound ∧ key = arrayEntrySlot (Nat.toB256 (i + 1)))

/-- The two Registry key families whose raw slot is packed through the
address mask (assignment, and a populated array entry within `bound`).
Only a write at one of these needs its value already canonical to read back
clean; the plain-word families (index, count, array length) never do, and a
write's value there need not even be address-shaped (a count, say).  Bounded
exactly like `RegistryObservable`'s own address-shaped disjuncts, so the
three plain families are refutable from it with no extra premise. -/
def RegistryAddressFamily (bound : Nat) (key : B256) : Prop :=
  (∃ probe, canonicalAddress probe ∧ key = assignmentSlot probe) ∨
  (∃ i, i < bound ∧ key = arrayEntrySlot (Nat.toB256 (i + 1)))

private theorem not_registryAddressFamily_indexSlot
    {bound : Nat} {probe : B256} (hprobe : canonicalAddress probe)
    (hlength : bound < 2 ^ 252) :
    ¬ RegistryAddressFamily bound (indexSlot probe) := by
  rintro (⟨p, hp, heq⟩ | ⟨i, hi, heq⟩)
  · exact (registryAddressFamilies_pairwise hp hprobe hprobe).1 heq.symm
  · have hb : (Nat.toB256 (i + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega : i + 1 < 2 ^ 256)]
      omega
    exact (registryAddressFamilies_ne_arrayEntrySlot hprobe hprobe hb).2.1 heq

private theorem not_registryAddressFamily_countSlot
    {bound : Nat} {pauser : B256} (hpauser : canonicalAddress pauser)
    (hlength : bound < 2 ^ 252) :
    ¬ RegistryAddressFamily bound (countSlot pauser) := by
  rintro (⟨p, hp, heq⟩ | ⟨i, hi, heq⟩)
  · exact (registryAddressFamilies_pairwise hp hp hpauser).2.1 heq.symm
  · have hb : (Nat.toB256 (i + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega : i + 1 < 2 ^ 256)]
      omega
    exact (registryAddressFamilies_ne_arrayEntrySlot hpauser hpauser hb).2.2 heq

private theorem not_registryAddressFamily_arrayLengthSlot
    {bound : Nat} (hlength : bound < 2 ^ 252) :
    ¬ RegistryAddressFamily bound arrayLengthSlot := by
  rintro (⟨p, hp, heq⟩ | ⟨i, hi, heq⟩)
  · exact (registryAddressFamilies_ne_arrayLengthSlot hp hp).1 heq.symm
  · have hb256 : i + 1 < 2 ^ 256 := by omega
    have hb : (Nat.toB256 (i + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt hb256]
      omega
    have hzero : (0 : B256).toNat < 2 ^ 252 := by
      rw [B256.toNat_zero]
      norm_num
    have hpayload : (0 : B256) = Nat.toB256 (i + 1) :=
      slot_injective_payload (region := arrayRegion) (left := (0 : B256))
        (right := Nat.toB256 (i + 1)) (by norm_num [arrayRegion]) hzero hb heq
    have hn := congrArg B256.toNat hpayload
    rw [B256.toNat_toB256_of_lt hb256] at hn
    simp only [B256.toNat_zero] at hn
    omega

/-- No other observed logical key shares a raw slot with a written key:
collision-freedom only at the finitely many written slots, never global
Keccak injectivity. -/
def RegistryKeysFaithful (bound : Nat) (T : List B256) : Prop :=
  ∀ t ∈ T, ∀ k, RegistryObservable bound k → solKey k = solKey t → k = t

theorem RegistryKeysFaithful.mono {bound : Nat} {T T' : List B256}
    (h : RegistryKeysFaithful bound T) (hsub : ∀ t ∈ T', t ∈ T) :
    RegistryKeysFaithful bound T' :=
  fun t ht k hk heq => h t (hsub t ht) k hk heq

/-- The actual raw `Stor.set` value for a logical write: packed through the
address mask for the two address-shaped families (assignment, populated
array entries), verbatim otherwise (index, count, array length). -/
def registryRawValue (key old value : B256) : B256 :=
  let region := key.toNat / 2 ^ 252
  let payload := Nat.toB256 (key.toNat % 2 ^ 252)
  if region = assignmentRegion then addressSlotWriteWord old value
  else if region = arrayRegion ∧ payload ≠ 0 then addressSlotWriteWord old value
  else value

private theorem registryRawValue_assignmentSlot {probe old value : B256}
    (h : canonicalAddress probe) :
    registryRawValue (assignmentSlot probe) old value = addressSlotWriteWord old value := by
  have h' := tagged_region_payload (region := assignmentRegion)
    (by norm_num [assignmentRegion]) (canonicalAddress_payload_lt h)
  simp only [assignmentSlot, registryRawValue, h'.1, h'.2]
  simp

private theorem registryRawValue_indexSlot {probe old value : B256}
    (h : canonicalAddress probe) :
    registryRawValue (indexSlot probe) old value = value := by
  have h' := tagged_region_payload (region := indexRegion)
    (by norm_num [indexRegion]) (canonicalAddress_payload_lt h)
  simp only [indexSlot, registryRawValue, h'.1, h'.2]
  simp [assignmentRegion, indexRegion, arrayRegion]

private theorem registryRawValue_countSlot {probe old value : B256}
    (h : canonicalAddress probe) :
    registryRawValue (countSlot probe) old value = value := by
  have h' := tagged_region_payload (region := countRegion)
    (by norm_num [countRegion]) (canonicalAddress_payload_lt h)
  simp only [countSlot, registryRawValue, h'.1, h'.2]
  simp [assignmentRegion, countRegion, arrayRegion]

private theorem registryRawValue_arrayLengthSlot {old value : B256} :
    registryRawValue arrayLengthSlot old value = value := by
  have h' := tagged_region_payload (region := arrayRegion) (payload := 0)
    (by norm_num [arrayRegion]) (by
      change (0 : Nat) < 2 ^ 252
      norm_num)
  simp only [arrayLengthSlot, registryRawValue, h'.1, h'.2]
  simp [assignmentRegion, arrayRegion]

private theorem registryRawValue_arrayEntrySlot {index : Nat} {old value : B256}
    (hindex : index + 1 < 2 ^ 252) :
    registryRawValue (arrayEntrySlot (Nat.toB256 (index + 1))) old value =
      addressSlotWriteWord old value := by
  have h256 : index + 1 < 2 ^ 256 := by omega
  have hword : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt h256]
    exact hindex
  have h' := tagged_region_payload (region := arrayRegion)
    (by norm_num [arrayRegion]) hword
  have hnonzero : Nat.toB256 (index + 1) ≠ 0 := by
    intro heq
    have hn := congrArg B256.toNat heq
    rw [B256.toNat_toB256_of_lt h256] at hn
    change index + 1 = 0 at hn
    omega
  simp only [arrayEntrySlot, registryRawValue, h'.1, h'.2]
  simp [assignmentRegion, arrayRegion, hnonzero]

/-- A chronological chain of logical Registry writes, applied at their raw
Solidity slots with the actual Solidity write shape (plain word, or a
packed-address read-modify-write) per key. -/
def applyRegistryRawWrites (raw : Stor) (writes : List (B256 × B256)) : Stor :=
  writes.foldl
    (fun s w => s.set (solKey w.1) (registryRawValue w.1 (s.get (solKey w.1)) w.2))
    raw

private theorem solRegistryStorage_read_congr
    {bound : Nat} {a b : Stor} {key : B256}
    (hlength : bound < 2 ^ 252)
    (hkey : RegistryObservable bound key)
    (h : a.get (solKey key) = b.get (solKey key)) :
    (solRegistryStorage a).read key = (solRegistryStorage b).read key := by
  rcases hkey with
    ⟨probe, hprobe, rfl⟩ | ⟨probe, hprobe, rfl⟩ | ⟨probe, hprobe, rfl⟩ |
      rfl | ⟨i, hi, rfl⟩
  · rw [solKey_assignmentSlot hprobe] at h
    rw [solRegistryStorage_assignment _ _ hprobe, solRegistryStorage_assignment _ _ hprobe, h]
  · rw [solKey_indexSlot hprobe] at h
    rw [solRegistryStorage_index _ _ hprobe, solRegistryStorage_index _ _ hprobe, h]
  · rw [solKey_countSlot hprobe] at h
    rw [solRegistryStorage_count _ _ hprobe, solRegistryStorage_count _ _ hprobe, h]
  · rw [solKey_arrayLengthSlot] at h
    rw [solRegistryStorage_length, solRegistryStorage_length, h]
  · have hbound : i + 1 < 2 ^ 252 := by omega
    rw [solKey_arrayEntrySlot hbound] at h
    rw [solRegistryStorage_array _ _ hbound, solRegistryStorage_array _ _ hbound, h]

private theorem solRegistryStorage_read_of_set
    {bound : Nat} {before : Stor} {logicalKey value : B256}
    (hlength : bound < 2 ^ 252)
    (hkey : RegistryObservable bound logicalKey)
    (hclean : RegistryAddressFamily bound logicalKey → addressSlotReadWord value = value) :
    (solRegistryStorage
      (before.set (solKey logicalKey)
        (registryRawValue logicalKey (before.get (solKey logicalKey)) value))
      ).read logicalKey = value := by
  rcases hkey with
    ⟨probe, hprobe, rfl⟩ | ⟨probe, hprobe, rfl⟩ | ⟨probe, hprobe, rfl⟩ |
      rfl | ⟨i, hi, rfl⟩
  · rw [solKey_assignmentSlot hprobe]
    rw [solRegistryStorage_assignment _ _ hprobe, Stor.get_set_ite, if_pos rfl,
      registryRawValue_assignmentSlot hprobe]
    exact addressSlotReadWord_write_of_clean _ _ (hclean (Or.inl ⟨probe, hprobe, rfl⟩))
  · rw [solKey_indexSlot hprobe]
    rw [solRegistryStorage_index _ _ hprobe, Stor.get_set_ite, if_pos rfl,
      registryRawValue_indexSlot hprobe]
  · rw [solKey_countSlot hprobe]
    rw [solRegistryStorage_count _ _ hprobe, Stor.get_set_ite, if_pos rfl,
      registryRawValue_countSlot hprobe]
  · rw [solKey_arrayLengthSlot]
    rw [solRegistryStorage_length, Stor.get_set_ite, if_pos rfl,
      registryRawValue_arrayLengthSlot]
  · have hbound : i + 1 < 2 ^ 252 := by omega
    rw [solKey_arrayEntrySlot hbound]
    rw [solRegistryStorage_array _ _ hbound, Stor.get_set_ite, if_pos rfl,
      registryRawValue_arrayEntrySlot hbound]
    exact addressSlotReadWord_write_of_clean _ _ (hclean (Or.inr ⟨i, hi, rfl⟩))

private theorem solRegistryStorage_step
    {bound : Nat} {before : Stor} {logicalKey value : B256}
    (hlength : bound < 2 ^ 252)
    (hkeyObs : RegistryObservable bound logicalKey)
    (hclean : RegistryAddressFamily bound logicalKey → addressSlotReadWord value = value)
    {key : B256} (hkey : RegistryObservable bound key)
    (hfaithfulOne : ∀ k, RegistryObservable bound k →
      solKey k = solKey logicalKey → k = logicalKey) :
    (solRegistryStorage
      (before.set (solKey logicalKey)
        (registryRawValue logicalKey (before.get (solKey logicalKey)) value))
      ).read key =
      if logicalKey = key then value else (solRegistryStorage before).read key := by
  by_cases heq : logicalKey = key
  · simp only [if_pos heq]
    rw [← heq]
    exact solRegistryStorage_read_of_set hlength hkeyObs hclean
  · simp only [if_neg heq]
    have hne : solKey logicalKey ≠ solKey key := by
      intro hcontra
      exact heq (hfaithfulOne key hkey hcontra.symm).symm
    apply solRegistryStorage_read_congr hlength hkey
    rw [Stor.get_set_ite, if_neg hne]

/-- **The unified raw-write transport lemma.**  Given the actual raw writes
of a chronological chain of logical Registry writes (plain words or
packed-address read-modify-writes, per `applyRegistryRawWrites`), and that
the written keys are `RegistryKeysFaithful` for the observed keys, every
observed logical key's Solidity-decoded value after the chain agrees with
the logical fold of the writes — the single fact each of the four native
transitions' raw analogues now consumes, in place of a bespoke
key-correspondence bundle. -/
theorem solRegistryStorage_applyRegistryRawWrites
    {bound : Nat} {before : Stor} {writes : List (B256 × B256)}
    (hlength : bound < 2 ^ 252)
    (hfaithful : RegistryKeysFaithful bound (writes.map Prod.fst))
    (hobservable : ∀ w ∈ writes, RegistryObservable bound w.1)
    (hclean : ∀ w ∈ writes, RegistryAddressFamily bound w.1 → addressSlotReadWord w.2 = w.2)
    {key : B256} (hkey : RegistryObservable bound key) :
    (solRegistryStorage (applyRegistryRawWrites before writes)).read key =
      writes.foldl (fun cur w => if w.1 = key then w.2 else cur)
        ((solRegistryStorage before).read key) := by
  induction writes generalizing before with
  | nil => rfl
  | cons w rest ih =>
    have hfaithfulRest : RegistryKeysFaithful bound (rest.map Prod.fst) :=
      hfaithful.mono (fun t ht => List.mem_cons_of_mem _ ht)
    have hobservableRest : ∀ w' ∈ rest, RegistryObservable bound w'.1 :=
      fun w' hw' => hobservable w' (List.mem_cons_of_mem _ hw')
    have hcleanRest : ∀ w' ∈ rest, RegistryAddressFamily bound w'.1 → addressSlotReadWord w'.2 = w'.2 :=
      fun w' hw' => hclean w' (List.mem_cons_of_mem _ hw')
    have hw1obs : RegistryObservable bound w.1 :=
      hobservable w List.mem_cons_self
    have hw1clean : RegistryAddressFamily bound w.1 → addressSlotReadWord w.2 = w.2 :=
      hclean w List.mem_cons_self
    have hfaithfulOne : ∀ k, RegistryObservable bound k →
        solKey k = solKey w.1 → k = w.1 :=
      fun k hk heq => hfaithful w.1 List.mem_cons_self k hk heq
    have hstep :
        (solRegistryStorage
          (before.set (solKey w.1) (registryRawValue w.1 (before.get (solKey w.1)) w.2))
          ).read key =
        if w.1 = key then w.2 else (solRegistryStorage before).read key :=
      solRegistryStorage_step hlength hw1obs hw1clean hkey hfaithfulOne
    show (solRegistryStorage
        (applyRegistryRawWrites
          (before.set (solKey w.1) (registryRawValue w.1 (before.get (solKey w.1)) w.2))
          rest)).read key =
      rest.foldl (fun cur w' => if w'.1 = key then w'.2 else cur)
        (if w.1 = key then w.2 else (solRegistryStorage before).read key)
    rw [← hstep]
    exact ih hfaithfulRest hobservableRest hcleanRest
      (before := before.set (solKey w.1) (registryRawValue w.1 (before.get (solKey w.1)) w.2))

/-- Combine the unified transport lemma with pointwise raw equality (the
form a later bytecode-walk proof supplies) to conclude the deployed
projection's `RegistryWitness` from the corresponding logical-fold witness. -/
theorem RegistryWitness.ofRawRegistryWrites
    {before after : Stor} {entries' : List Entry} {bound : Nat}
    {writes : List (B256 × B256)}
    (hlength : bound < 2 ^ 252)
    (hboundPost : entries'.length ≤ bound)
    (hfaithful : RegistryKeysFaithful bound (writes.map Prod.fst))
    (hobservable : ∀ w ∈ writes, RegistryObservable bound w.1)
    (hclean : ∀ w ∈ writes, RegistryAddressFamily bound w.1 → addressSlotReadWord w.2 = w.2)
    (hwrites : ∀ key, after.get key = (applyRegistryRawWrites before writes).get key)
    (hlogical : RegistryWitness
      { read := fun key => writes.foldl (fun cur w => if w.1 = key then w.2 else cur)
          ((solRegistryStorage before).read key) } entries') :
    RegistryWitness (solRegistryStorage after) entries' := by
  have hread : ∀ key, RegistryObservable bound key →
      (solRegistryStorage after).read key =
        writes.foldl (fun cur w => if w.1 = key then w.2 else cur)
          ((solRegistryStorage before).read key) := by
    intro key hkey
    have hcongr := solRegistryStorage_read_congr (bound := bound) (key := key)
      hlength hkey (a := after) (b := applyRegistryRawWrites before writes)
      (by rw [hwrites])
    rw [hcongr]
    exact solRegistryStorage_applyRegistryRawWrites hlength hfaithful hobservable hclean hkey
  exact {
    targetsNodup := hlogical.targetsNodup
    targetsValid := hlogical.targetsValid
    pausersValid := hlogical.pausersValid
    lengthWord := by
      rw [hread arrayLengthSlot (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
      exact hlogical.lengthWord
    arrayWords := by
      intro probe hprobe
      rw [hread _ (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨probe, by omega, rfl⟩))))]
      exact hlogical.arrayWords probe hprobe
    assignments := by
      intro probe hprobe
      rw [hread _ (Or.inl ⟨probe, hprobe, rfl⟩)]
      exact hlogical.assignments probe hprobe
    indices := by
      intro probe hprobe
      rw [hread _ (Or.inr (Or.inl ⟨probe, hprobe, rfl⟩))]
      exact hlogical.indices probe hprobe
    counts := by
      intro probe hprobe
      rw [hread _ (Or.inr (Or.inr (Or.inl ⟨probe, hprobe, rfl⟩)))]
      exact hlogical.counts probe hprobe
    zeroCount := by
      have hzero : canonicalAddress (0 : B256) := by
        unfold canonicalAddress
        change (0 : Nat) < 2 ^ 160
        norm_num
      rw [hread _ (Or.inr (Or.inr (Or.inl ⟨0, hzero, rfl⟩)))]
      exact hlogical.zeroCount
  }

/-- A functional post-observation with the same seven logical writes as the
native Registry removal.  This is used only to share its preservation proof. -/
def logicalRemovalPost (before : LogicalStorage) (entries : List Entry)
    (target oldPauser : B256) (index : Nat) : LogicalStorage :=
  { read := fun key =>
      [(assignmentSlot target, 0),
       (countSlot oldPauser,
         Nat.toB256 (assignmentCount entries oldPauser - 1)),
       (arrayEntrySlot (Nat.toB256 (index + 1)), sourceLastTarget entries),
       (indexSlot (sourceLastTarget entries), Nat.toB256 (index + 1)),
       (arrayEntrySlot (Nat.toB256 entries.length), 0),
       (arrayLengthSlot, Nat.toB256 (entries.length - 1)),
       (indexSlot target, 0)].foldl
        (fun current write => if write.1 = key then write.2 else current)
        (before.read key) }

/-- The actual raw Solidity write order for the found-target removal path.
Address writes retain the old high 96 bits, including on clears. -/
def rawRemovalPost (raw : Stor) (entries : List Entry)
    (target oldPauser : B256) (index : Nat) : Stor :=
  let assignmentKey := mapSlot target 3
  let countKey := mapSlot oldPauser 6
  let holeKey := registryArraySlot index
  let movedIndexKey := mapSlot (sourceLastTarget entries) 4
  let tailKey := registryArraySlot (entries.length - 1)
  let lengthKey : B256 := 5
  let targetIndexKey := mapSlot target 4
  let s1 := raw.set assignmentKey
    (addressSlotWriteWord (raw.get assignmentKey) 0)
  let s2 := s1.set countKey
    (Nat.toB256 (assignmentCount entries oldPauser - 1))
  let s3 := s2.set holeKey
    (addressSlotWriteWord (s2.get holeKey) (sourceLastTarget entries))
  let s4 := s3.set movedIndexKey (Nat.toB256 (index + 1))
  let s5 := s4.set tailKey
    (addressSlotWriteWord (s4.get tailKey) 0)
  let s6 := s5.set lengthKey (Nat.toB256 (entries.length - 1))
  s6.set targetIndexKey 0

/-- A pointwise, raw-storage effect contract for the bytecode walk.  It states
the seven actual `Stor.set` effects, and the local agreement of their observed
Solidity families with the chronological logical fold.  The second part is
where local touched-key separation is discharged; neither clause assumes a
post-`RegistryWitness` or global Keccak injectivity. -/
structure RawRemovalReadEffect (before after : Stor) (entries : List Entry)
    (target oldPauser : B256) (index : Nat) : Prop where
  writes : ∀ key, after.get key =
    (rawRemovalPost before entries target oldPauser index).get key
  assignments : ∀ probe, canonicalAddress probe →
    addressSlotReadWord
      ((rawRemovalPost before entries target oldPauser index).get
        (mapSlot probe 3)) =
      (logicalRemovalPost (solRegistryStorage before) entries
        target oldPauser index).read (assignmentSlot probe)
  indices : ∀ probe, canonicalAddress probe →
    (rawRemovalPost before entries target oldPauser index).get
      (mapSlot probe 4) =
      (logicalRemovalPost (solRegistryStorage before) entries
        target oldPauser index).read (indexSlot probe)
  counts : ∀ probe, canonicalAddress probe →
    (rawRemovalPost before entries target oldPauser index).get
      (mapSlot probe 6) =
      (logicalRemovalPost (solRegistryStorage before) entries
        target oldPauser index).read (countSlot probe)
  length : (rawRemovalPost before entries target oldPauser index).get 5 =
    (logicalRemovalPost (solRegistryStorage before) entries
      target oldPauser index).read arrayLengthSlot
  array : ∀ probe, probe + 1 < entries.length →
    addressSlotReadWord
      ((rawRemovalPost before entries target oldPauser index).get
        (registryArraySlot probe)) =
      (logicalRemovalPost (solRegistryStorage before) entries
        target oldPauser index).read
          (arrayEntrySlot (Nat.toB256 (probe + 1)))

/-- The deployed storage projection consumes the shared swap/pop proof once
the raw seven-store effect and local observation equations have been shown. -/
theorem RawRemovalReadEffect.preservesRegistry
    {before after : Stor} {entries : List Entry}
    {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage before) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (heffect : RawRemovalReadEffect before after entries target oldPauser index) :
    RegistryWitness (solRegistryStorage after) (swapPop entries index) := by
  have hlogical : RegistryWitness
      (logicalRemovalPost (solRegistryStorage before) entries
        target oldPauser index) (swapPop entries index) := by
    apply RegistryWitness.applyFoundZeroWritesOfReadEffect hw htarget hfind
    intro key
    rfl
  exact {
    targetsNodup := hlogical.targetsNodup
    targetsValid := hlogical.targetsValid
    pausersValid := hlogical.pausersValid
    lengthWord := by
      rw [solRegistryStorage_length, heffect.writes,
        heffect.length]
      exact hlogical.lengthWord
    arrayWords := by
      intro probe hprobe
      have hbound : probe + 1 < 2 ^ 252 := by
        rw [swapPop_length_of_findEntry hfind] at hprobe
        have hlength := hw.entries_length_lt_2pow252
        omega
      rw [solRegistryStorage_array _ _ hbound, heffect.writes]
      rw [heffect.array probe (by
        rw [swapPop_length_of_findEntry hfind] at hprobe
        omega)]
      exact hlogical.arrayWords probe hprobe
    assignments := by
      intro probe hprobe
      rw [solRegistryStorage_assignment _ _ hprobe, heffect.writes,
        heffect.assignments probe hprobe]
      exact hlogical.assignments probe hprobe
    indices := by
      intro probe hprobe
      rw [solRegistryStorage_index _ _ hprobe, heffect.writes,
        heffect.indices probe hprobe]
      exact hlogical.indices probe hprobe
    counts := by
      intro probe hprobe
      rw [solRegistryStorage_count _ _ hprobe, heffect.writes,
        heffect.counts probe hprobe]
      exact hlogical.counts probe hprobe
    zeroCount := by
      have hzero : canonicalAddress (0 : B256) := by
        unfold canonicalAddress
        change (0 : Nat) < 2 ^ 160
        norm_num
      rw [solRegistryStorage_count _ _ hzero, heffect.writes,
        heffect.counts 0 hzero]
      exact hlogical.zeroCount
  }

/-- A functional post-observation with the same five logical writes as the
native fresh-registration Registry transition.  This is used only to share
its preservation proof. -/
def logicalFreshPost (before : LogicalStorage) (entries : List Entry)
    (target newPauser : B256) : LogicalStorage :=
  { read := fun key =>
      [(assignmentSlot target, newPauser),
       (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
       (indexSlot target, Nat.toB256 (entries.length + 1)),
       (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
       (countSlot newPauser,
         Nat.toB256 (assignmentCount entries newPauser + 1))].foldl
        (fun current write => if write.1 = key then write.2 else current)
        (before.read key) }

/-- The actual raw Solidity write order for the fresh-registration path.
Address writes retain the old high 96 bits, including on the new entry. -/
def rawFreshPost (raw : Stor) (entries : List Entry)
    (target newPauser : B256) : Stor :=
  let assignmentKey := mapSlot target 3
  let arrayKey := registryArraySlot entries.length
  let indexKey := mapSlot target 4
  let lengthKey : B256 := 5
  let countKey := mapSlot newPauser 6
  let s1 := raw.set assignmentKey
    (addressSlotWriteWord (raw.get assignmentKey) newPauser)
  let s2 := s1.set arrayKey
    (addressSlotWriteWord (s1.get arrayKey) target)
  let s3 := s2.set indexKey (Nat.toB256 (entries.length + 1))
  let s4 := s3.set lengthKey (Nat.toB256 (entries.length + 1))
  s4.set countKey (Nat.toB256 (assignmentCount entries newPauser + 1))

/-- A pointwise, raw-storage effect contract for the fresh-registration
bytecode walk.  It states the five actual `Stor.set` effects, and the local
agreement of their observed Solidity families with the chronological logical
fold.  The second part is where local touched-key separation is discharged;
neither clause assumes a post-`RegistryWitness` or global Keccak
injectivity. -/
structure RawFreshReadEffect (before after : Stor) (entries : List Entry)
    (target newPauser : B256) : Prop where
  writes : ∀ key, after.get key =
    (rawFreshPost before entries target newPauser).get key
  assignments : ∀ probe, canonicalAddress probe →
    addressSlotReadWord
      ((rawFreshPost before entries target newPauser).get
        (mapSlot probe 3)) =
      (logicalFreshPost (solRegistryStorage before) entries
        target newPauser).read (assignmentSlot probe)
  indices : ∀ probe, canonicalAddress probe →
    (rawFreshPost before entries target newPauser).get
      (mapSlot probe 4) =
      (logicalFreshPost (solRegistryStorage before) entries
        target newPauser).read (indexSlot probe)
  counts : ∀ probe, canonicalAddress probe →
    (rawFreshPost before entries target newPauser).get
      (mapSlot probe 6) =
      (logicalFreshPost (solRegistryStorage before) entries
        target newPauser).read (countSlot probe)
  length : (rawFreshPost before entries target newPauser).get 5 =
    (logicalFreshPost (solRegistryStorage before) entries
      target newPauser).read arrayLengthSlot
  array : ∀ probe, probe < entries.length + 1 →
    addressSlotReadWord
      ((rawFreshPost before entries target newPauser).get
        (registryArraySlot probe)) =
      (logicalFreshPost (solRegistryStorage before) entries
        target newPauser).read
          (arrayEntrySlot (Nat.toB256 (probe + 1)))

/-- The deployed storage projection consumes the shared fresh-registration
preservation proof once the raw five-store effect and local observation
equations have been shown. -/
theorem RawFreshReadEffect.preservesRegistry
    {before after : Stor} {entries : List Entry}
    {target newPauser : B256}
    (hw : RegistryWitness (solRegistryStorage before) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = none)
    (heffect : RawFreshReadEffect before after entries target newPauser) :
    RegistryWitness (solRegistryStorage after)
      (entries ++ [(target, newPauser)]) := by
  have hlogical : RegistryWitness
      (logicalFreshPost (solRegistryStorage before) entries target newPauser)
      (entries ++ [(target, newPauser)]) := by
    apply RegistryWitness.applyFreshWritesOfReadEffect hw htarget hnew hfind
    intro key
    rfl
  exact {
    targetsNodup := hlogical.targetsNodup
    targetsValid := hlogical.targetsValid
    pausersValid := hlogical.pausersValid
    lengthWord := by
      rw [solRegistryStorage_length, heffect.writes, heffect.length]
      exact hlogical.lengthWord
    arrayWords := by
      intro probe hprobe
      simp only [List.length_append, List.length_cons, List.length_nil]
        at hprobe
      have hbound : probe + 1 < 2 ^ 252 := by
        have hlength := hw.fresh_length_lt_2pow252
        omega
      rw [solRegistryStorage_array _ _ hbound, heffect.writes]
      rw [heffect.array probe hprobe]
      exact hlogical.arrayWords probe (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega)
    assignments := by
      intro probe hprobe
      rw [solRegistryStorage_assignment _ _ hprobe, heffect.writes,
        heffect.assignments probe hprobe]
      exact hlogical.assignments probe hprobe
    indices := by
      intro probe hprobe
      rw [solRegistryStorage_index _ _ hprobe, heffect.writes,
        heffect.indices probe hprobe]
      exact hlogical.indices probe hprobe
    counts := by
      intro probe hprobe
      rw [solRegistryStorage_count _ _ hprobe, heffect.writes,
        heffect.counts probe hprobe]
      exact hlogical.counts probe hprobe
    zeroCount := by
      have hzero : canonicalAddress (0 : B256) := by
        unfold canonicalAddress
        change (0 : Nat) < 2 ^ 160
        norm_num
      rw [solRegistryStorage_count _ _ hzero, heffect.writes,
        heffect.counts 0 hzero]
      exact hlogical.zeroCount
  }

/-! ## Found-nonzero and absent-zero: the raw layer straight from the
unified premise

Unlike removal and fresh above (whose raw-write structs and proofs predate
this module's transport lemma), these two transitions are stated directly
against `RegistryKeysFaithful`/`applyRegistryRawWrites`/
`RegistryWitness.ofRawRegistryWrites` from the start; there is no
per-transition `RawXReadEffect` bundle to keep in step. -/

/-- The three chronological logical writes for reassigning an existing
target to a nonzero pauser: exactly `applyFoundNonzeroWritesOfReadEffect`'s
write list (`Blanc/LidoCircuitBreakerRegistry.lean`). -/
def nonzeroWrites (entries : List Entry) (target newPauser oldPauser : B256) :
    List (B256 × B256) :=
  [(assignmentSlot target, newPauser),
   (countSlot oldPauser, Nat.toB256 (assignmentCount entries oldPauser - 1)),
   (countSlot newPauser,
     Nat.toB256 ((assignmentCount entries newPauser -
       (if oldPauser = newPauser then 1 else 0)) + 1))]

/-- The actual raw Solidity write order for the found-target,
nonzero-new-pauser reassignment path: `pauser[target] = newPauser`, then the
old pauser's decrement, then the new pauser's increment.  The two count
slots may alias when `oldPauser = newPauser`; the chronological fold handles
that the same way `nonzeroWrites`' logical fold does, since both are the
same list applied in the same order. -/
def rawNonzeroPost (raw : Stor) (entries : List Entry)
    (target newPauser oldPauser : B256) : Stor :=
  applyRegistryRawWrites raw (nonzeroWrites entries target newPauser oldPauser)

/-- Concrete application of the shared logical three-write preservation
theorem to the deployed Solidity storage projection: the found-target,
nonzero-new-pauser reassignment. -/
theorem rawNonzero_preservesRegistry
    {before after : Stor} {entries : List Entry}
    {target newPauser oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage before) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : RegistryKeysFaithful entries.length
      ((nonzeroWrites entries target newPauser oldPauser).map Prod.fst))
    (hwrites : ∀ key, after.get key =
      (rawNonzeroPost before entries target newPauser oldPauser).get key) :
    RegistryWitness (solRegistryStorage after)
      (setEntryAt index (target, newPauser) entries) := by
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hlogical : RegistryWitness
      { read := fun key => (nonzeroWrites entries target newPauser oldPauser).foldl
          (fun cur w => if w.1 = key then w.2 else cur)
          ((solRegistryStorage before).read key) }
      (setEntryAt index (target, newPauser) entries) := by
    apply RegistryWitness.applyFoundNonzeroWritesOfReadEffect hw htarget hnew hfind
    intro key
    rfl
  refine RegistryWitness.ofRawRegistryWrites
    hw.entries_length_lt_2pow252 ?_ hfaithful ?_ ?_ hwrites hlogical
  · rw [setEntryAt_length_of_findEntry hfind]
  · intro w hw'
    simp only [nonzeroWrites, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact Or.inl ⟨target, htarget.2, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨oldPauser, hold.2, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨newPauser, hnew.2, rfl⟩))
  · intro w hw' hfam
    simp only [nonzeroWrites, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact addressSlotReadWord_eq_self_of_lt hnew.2
    · exact absurd hfam
        (not_registryAddressFamily_countSlot hold.2 hw.entries_length_lt_2pow252)
    · exact absurd hfam
        (not_registryAddressFamily_countSlot hnew.2 hw.entries_length_lt_2pow252)

/-- The nine chronological logical writes for an absent-target,
zero-new-pauser call: exactly `applyAbsentZeroWritesOfReadEffect`'s write
list (`Blanc/LidoCircuitBreakerRegistry.lean`).  A fresh push immediately
undone by the swap-pop removal branch, since `_newPauser = 0` there too; the
entries list is unchanged, but the nine physical writes still happen. -/
def absentZeroWrites (entries : List Entry) (target : B256) :
    List (B256 × B256) :=
  [(assignmentSlot target, 0),
   (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
   (indexSlot target, Nat.toB256 (entries.length + 1)),
   (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
   (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
   (indexSlot target, Nat.toB256 (entries.length + 1)),
   (arrayEntrySlot (Nat.toB256 (entries.length + 1)), 0),
   (arrayLengthSlot, Nat.toB256 entries.length),
   (indexSlot target, 0)]

/-- The actual raw Solidity write order for the absent-target,
zero-new-pauser path. -/
def rawAbsentZeroPost (raw : Stor) (entries : List Entry) (target : B256) : Stor :=
  applyRegistryRawWrites raw (absentZeroWrites entries target)

/-- Concrete application of the shared logical nine-write preservation
theorem to the deployed Solidity storage projection: the absent-target,
zero-new-pauser call. -/
theorem rawAbsentZero_preservesRegistry
    {before after : Stor} {entries : List Entry} {target : B256}
    (hw : RegistryWitness (solRegistryStorage before) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = none)
    (hfaithful : RegistryKeysFaithful (entries.length + 1)
      ((absentZeroWrites entries target).map Prod.fst))
    (hwrites : ∀ key, after.get key =
      (rawAbsentZeroPost before entries target).get key) :
    RegistryWitness (solRegistryStorage after) entries := by
  have hlogical : RegistryWitness
      { read := fun key => (absentZeroWrites entries target).foldl
          (fun cur w => if w.1 = key then w.2 else cur)
          ((solRegistryStorage before).read key) }
      entries := by
    apply RegistryWitness.applyAbsentZeroWritesOfReadEffect hw htarget hfind
    intro key
    rfl
  have hlengthLt : entries.length + 1 < 2 ^ 252 := hw.fresh_length_lt_2pow252
  refine RegistryWitness.ofRawRegistryWrites
    hlengthLt ?_ hfaithful ?_ ?_ hwrites hlogical
  · omega
  · intro w hw'
    have harr : entries.length < entries.length + 1 := by omega
    simp only [absentZeroWrites, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨target, htarget.2, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨entries.length, harr, rfl⟩)))
    · exact Or.inr (Or.inl ⟨target, htarget.2, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨entries.length, harr, rfl⟩)))
    · exact Or.inr (Or.inl ⟨target, htarget.2, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨entries.length, harr, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inl ⟨target, htarget.2, rfl⟩)
  · intro w hw' hfam
    have hzero : canonicalAddress (0 : B256) := by
      unfold canonicalAddress
      change (0 : Nat) < 2 ^ 160
      norm_num
    simp only [absentZeroWrites, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact addressSlotReadWord_eq_self_of_lt hzero
    · exact addressSlotReadWord_eq_self_of_lt htarget.2
    · exact absurd hfam (not_registryAddressFamily_indexSlot htarget.2 hlengthLt)
    · exact absurd hfam (not_registryAddressFamily_arrayLengthSlot hlengthLt)
    · exact addressSlotReadWord_eq_self_of_lt htarget.2
    · exact absurd hfam (not_registryAddressFamily_indexSlot htarget.2 hlengthLt)
    · exact addressSlotReadWord_eq_self_of_lt hzero
    · exact absurd hfam (not_registryAddressFamily_arrayLengthSlot hlengthLt)
    · exact absurd hfam (not_registryAddressFamily_indexSlot htarget.2 hlengthLt)

end Blanc.Lift.LidoCircuitBreakerDeployed
