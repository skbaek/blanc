import Blanc.Lift.LidoCircuitBreakerDeployed.RegistryLayout

/-! Local key separation and observable effects of the deployed Registry's
seven chronological removal writes. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc.LidoCircuitBreaker

/-- The seven write positions, retained in execution order. -/
inductive RemovalWrite where
  | assignment | count | hole | movedIndex | tail | length | removedIndex

/-- Physical Solidity key touched at a removal write position. -/
def removalRawKey (entries : List Entry) (target oldPauser : B256)
    (index : Nat) : RemovalWrite → B256
  | .assignment => mapSlot target 3
  | .count => mapSlot oldPauser 6
  | .hole => registryArraySlot index
  | .movedIndex => mapSlot (sourceLastTarget entries) 4
  | .tail => registryArraySlot (entries.length - 1)
  | .length => 5
  | .removedIndex => mapSlot target 4

/-- Tagged logical key corresponding to each physical removal write. -/
def removalLogicalKey (entries : List Entry) (target oldPauser : B256)
    (index : Nat) : RemovalWrite → B256
  | .assignment => assignmentSlot target
  | .count => countSlot oldPauser
  | .hole => arrayEntrySlot (Nat.toB256 (index + 1))
  | .movedIndex => indexSlot (sourceLastTarget entries)
  | .tail => arrayEntrySlot (Nat.toB256 entries.length)
  | .length => arrayLengthSlot
  | .removedIndex => indexSlot target

/-- Collision correspondence only at the seven touched keys. It admits
aliases whenever both the physical and logical keys alias. -/
def RemovalKeyCorrespondence (entries : List Entry)
    (target oldPauser : B256) (index : Nat)
    (rawKey logicalKey : B256) : Prop :=
  ∀ write : RemovalWrite,
    rawKey = removalRawKey entries target oldPauser index write ↔
      logicalKey = removalLogicalKey entries target oldPauser index write

/-- Separation hypotheses for exactly the observed Registry families.
The array premise includes the old tail, although it is no longer active in
the post-witness. The count premise includes zero. -/
structure LocalRemovalKeys (entries : List Entry)
    (target oldPauser : B256) (index : Nat) : Prop where
  assignments : ∀ probe, canonicalAddress probe →
    RemovalKeyCorrespondence entries target oldPauser index
      (mapSlot probe 3) (assignmentSlot probe)
  indices : ∀ probe, canonicalAddress probe →
    RemovalKeyCorrespondence entries target oldPauser index
      (mapSlot probe 4) (indexSlot probe)
  counts : ∀ probe, canonicalAddress probe →
    RemovalKeyCorrespondence entries target oldPauser index
      (mapSlot probe 6) (countSlot probe)
  length : RemovalKeyCorrespondence entries target oldPauser index
      5 arrayLengthSlot
  array : ∀ probe, probe < entries.length →
    RemovalKeyCorrespondence entries target oldPauser index
      (registryArraySlot probe)
      (arrayEntrySlot (Nat.toB256 (probe + 1)))

private theorem address_observation_effect
    (raw : Stor) (entries : List Entry) (target oldPauser : B256)
    (index : Nat) (rawKey logicalKey : B256)
    (hkeys : RemovalKeyCorrespondence entries target oldPauser index
      rawKey logicalKey)
    (hbase : addressSlotReadWord (raw.get rawKey) =
      (solRegistryStorage raw).read logicalKey)
    (hclean : addressSlotReadWord (sourceLastTarget entries) =
      sourceLastTarget entries)
    (hcount : logicalKey ≠ countSlot oldPauser)
    (hmoved : logicalKey ≠ indexSlot (sourceLastTarget entries))
    (hlength : logicalKey ≠ arrayLengthSlot)
    (hremoved : logicalKey ≠ indexSlot target) :
    addressSlotReadWord
      ((rawRemovalPost raw entries target oldPauser index).get rawKey) =
      (logicalRemovalPost (solRegistryStorage raw) entries
        target oldPauser index).read logicalKey := by
  have hcountRaw : mapSlot oldPauser 6 ≠ rawKey := by
    intro h
    exact hcount ((hkeys .count).mp h.symm)
  have hmovedRaw : mapSlot (sourceLastTarget entries) 4 ≠ rawKey := by
    intro h
    exact hmoved ((hkeys .movedIndex).mp h.symm)
  have hlengthRaw : (5 : B256) ≠ rawKey := by
    intro h
    exact hlength ((hkeys .length).mp h.symm)
  have hremovedRaw : mapSlot target 4 ≠ rawKey := by
    intro h
    exact hremoved ((hkeys .removedIndex).mp h.symm)
  have hassignmentKey :
      mapSlot target 3 = rawKey ↔ assignmentSlot target = logicalKey := by
    simpa [removalRawKey, removalLogicalKey, eq_comm] using
      (hkeys .assignment)
  have hholeKey :
      registryArraySlot index = rawKey ↔
        arrayEntrySlot (Nat.toB256 (index + 1)) = logicalKey := by
    simpa [removalRawKey, removalLogicalKey, eq_comm] using
      (hkeys .hole)
  have htailKey :
      registryArraySlot (entries.length - 1) = rawKey ↔
        arrayEntrySlot (Nat.toB256 entries.length) = logicalKey := by
    simpa [removalRawKey, removalLogicalKey, eq_comm] using
      (hkeys .tail)
  have hraw :
      addressSlotReadWord
        ((rawRemovalPost raw entries target oldPauser index).get rawKey) =
      if registryArraySlot (entries.length - 1) = rawKey then 0
      else if registryArraySlot index = rawKey then sourceLastTarget entries
      else if mapSlot target 3 = rawKey then 0
      else addressSlotReadWord (raw.get rawKey) := by
    unfold rawRemovalPost
    rw [Stor.get_set_ne _ hremovedRaw,
      Stor.get_set_ne _ hlengthRaw]
    rw [addressSlotReadWord_get_set_packed _ _ _ _ (by rfl)]
    by_cases htail : registryArraySlot (entries.length - 1) = rawKey
    · simp only [ite_eq_left htail]
    · simp only [ite_eq_right htail]
      rw [Stor.get_set_ne _ hmovedRaw]
      rw [addressSlotReadWord_get_set_packed _ _ _ _ hclean]
      by_cases hhole : registryArraySlot index = rawKey
      · simp only [ite_eq_left hhole]
      · simp only [ite_eq_right hhole]
        rw [Stor.get_set_ne _ hcountRaw]
        rw [addressSlotReadWord_get_set_packed _ _ _ _ (by rfl)]
  have hlogical :
      (logicalRemovalPost (solRegistryStorage raw) entries
        target oldPauser index).read logicalKey =
      if arrayEntrySlot (Nat.toB256 entries.length) = logicalKey then 0
      else if arrayEntrySlot (Nat.toB256 (index + 1)) = logicalKey then
        sourceLastTarget entries
      else if assignmentSlot target = logicalKey then 0
      else (solRegistryStorage raw).read logicalKey := by
    simp [logicalRemovalPost, Ne.symm hcount, Ne.symm hmoved,
      Ne.symm hlength, Ne.symm hremoved]
  rw [hraw, hlogical, hbase]
  simp only [hassignmentKey, hholeKey, htailKey]

private theorem word_observation_effect
    (raw : Stor) (entries : List Entry) (target oldPauser : B256)
    (index : Nat) (rawKey logicalKey : B256)
    (hkeys : RemovalKeyCorrespondence entries target oldPauser index
      rawKey logicalKey)
    (hbase : raw.get rawKey = (solRegistryStorage raw).read logicalKey)
    (hassignment : logicalKey ≠ assignmentSlot target)
    (hhole : logicalKey ≠ arrayEntrySlot (Nat.toB256 (index + 1)))
    (htail : logicalKey ≠ arrayEntrySlot (Nat.toB256 entries.length)) :
    (rawRemovalPost raw entries target oldPauser index).get rawKey =
      (logicalRemovalPost (solRegistryStorage raw) entries
        target oldPauser index).read logicalKey := by
  have hassignmentRaw : mapSlot target 3 ≠ rawKey := by
    intro h
    exact hassignment ((hkeys .assignment).mp h.symm)
  have hholeRaw : registryArraySlot index ≠ rawKey := by
    intro h
    exact hhole ((hkeys .hole).mp h.symm)
  have htailRaw : registryArraySlot (entries.length - 1) ≠ rawKey := by
    intro h
    exact htail ((hkeys .tail).mp h.symm)
  have hcountKey :
      mapSlot oldPauser 6 = rawKey ↔ countSlot oldPauser = logicalKey := by
    simpa [removalRawKey, removalLogicalKey, eq_comm] using
      (hkeys .count)
  have hmovedKey :
      mapSlot (sourceLastTarget entries) 4 = rawKey ↔
        indexSlot (sourceLastTarget entries) = logicalKey := by
    simpa [removalRawKey, removalLogicalKey, eq_comm] using
      (hkeys .movedIndex)
  have hlengthKey :
      (5 : B256) = rawKey ↔ arrayLengthSlot = logicalKey := by
    simpa [removalRawKey, removalLogicalKey, eq_comm] using
      (hkeys .length)
  have hremovedKey :
      mapSlot target 4 = rawKey ↔ indexSlot target = logicalKey := by
    simpa [removalRawKey, removalLogicalKey, eq_comm] using
      (hkeys .removedIndex)
  have hraw :
      (rawRemovalPost raw entries target oldPauser index).get rawKey =
      if mapSlot target 4 = rawKey then 0
      else if (5 : B256) = rawKey then
        Nat.toB256 (entries.length - 1)
      else if mapSlot (sourceLastTarget entries) 4 = rawKey then
        Nat.toB256 (index + 1)
      else if mapSlot oldPauser 6 = rawKey then
        Nat.toB256 (assignmentCount entries oldPauser - 1)
      else raw.get rawKey := by
    unfold rawRemovalPost
    rw [Stor.get_set_ite]
    by_cases hremoved : mapSlot target 4 = rawKey
    · simp only [ite_eq_left hremoved]
    · simp only [ite_eq_right hremoved]
      rw [Stor.get_set_ite]
      by_cases hlength : (5 : B256) = rawKey
      · simp only [ite_eq_left hlength]
      · simp only [ite_eq_right hlength]
        rw [Stor.get_set_ne _ htailRaw]
        rw [Stor.get_set_ite]
        by_cases hmoved : mapSlot (sourceLastTarget entries) 4 = rawKey
        · simp only [ite_eq_left hmoved]
        · simp only [ite_eq_right hmoved]
          rw [Stor.get_set_ne _ hholeRaw]
          rw [Stor.get_set_ite]
          by_cases hcount : mapSlot oldPauser 6 = rawKey
          · simp only [ite_eq_left hcount]
          · simp only [ite_eq_right hcount]
            rw [Stor.get_set_ne _ hassignmentRaw]
  have hlogical :
      (logicalRemovalPost (solRegistryStorage raw) entries
        target oldPauser index).read logicalKey =
      if indexSlot target = logicalKey then 0
      else if arrayLengthSlot = logicalKey then
        Nat.toB256 (entries.length - 1)
      else if indexSlot (sourceLastTarget entries) = logicalKey then
        Nat.toB256 (index + 1)
      else if countSlot oldPauser = logicalKey then
        Nat.toB256 (assignmentCount entries oldPauser - 1)
      else (solRegistryStorage raw).read logicalKey := by
    simp [logicalRemovalPost, Ne.symm hassignment, Ne.symm hhole,
      Ne.symm htail]
  rw [hraw, hlogical, hbase]
  simp only [hcountKey, hmovedKey, hlengthKey, hremovedKey]

/-- Local seven-key correspondence suffices for every Registry observation
after the actual packed/raw store sequence, including last-entry aliases. -/
theorem rawRemovalReadEffect_of_local_keys
    {raw : Stor} {entries : List Entry}
    {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage raw) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hkeys : LocalRemovalKeys entries target oldPauser index) :
    RawRemovalReadEffect raw
      (rawRemovalPost raw entries target oldPauser index)
      entries target oldPauser index := by
  have hfoundLt := findEntry_index_lt hfind
  have htailIndex : entries.length - 1 < entries.length := by omega
  have hholeLengthSep : arrayLengthSlot ≠
      arrayEntrySlot (Nat.toB256 (index + 1)) :=
    hw.arrayLengthSlot_ne_arrayEntrySlot hfoundLt
  have htailLengthSep : arrayLengthSlot ≠
      arrayEntrySlot (Nat.toB256 entries.length) := by
    have htailWord : entries.length - 1 + 1 = entries.length := by omega
    simpa only [htailWord] using
      (hw.arrayLengthSlot_ne_arrayEntrySlot htailIndex)
  have hlengthLt := hw.entries_length_lt_2pow252
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  obtain ⟨last, hlast⟩ := last_some_of_findEntry hfind
  have hlastValid : nonzeroCanonicalAddress last.1 :=
    hw.targetsValid last (last_mem_of_last entries hlast)
  have hm : nonzeroCanonicalAddress (sourceLastTarget entries) := by
    simpa [sourceLastTarget, hlast] using hlastValid
  have hmClean : addressSlotReadWord (sourceLastTarget entries) =
      sourceLastTarget entries := by
    have hlastBound : entries.length - 1 + 1 < 2 ^ 252 := by omega
    have harray := hw.arrayWords (entries.length - 1) htailIndex
    rw [solRegistryStorage_array _ _ hlastBound,
      targetAt_last_of_last entries hlast] at harray
    have hsource : sourceLastTarget entries = last.1 := by
      simp [sourceLastTarget, hlast]
    rw [hsource]
    calc
      addressSlotReadWord last.1 =
          addressSlotReadWord
            (addressSlotReadWord
              (raw.get (registryArraySlot (entries.length - 1)))) := by
                rw [harray]
      _ = addressSlotReadWord
            (raw.get (registryArraySlot (entries.length - 1))) := by
          rw [addressSlotReadWord_eq_toAdr_toB256
            (raw.get (registryArraySlot (entries.length - 1)))]
          exact addressSlotReadWord_toB256 _
      _ = last.1 := harray
  refine {
    writes := by intro key; rfl
    assignments := ?_
    indices := ?_
    counts := ?_
    length := ?_
    array := ?_ }
  · intro probe hprobe
    have hpairM := registryAddressFamilies_pairwise hprobe hm.2 hold.2
    have hpairT := registryAddressFamilies_pairwise
      hprobe htarget.2 hold.2
    have hlengthFam :=
      registryAddressFamilies_ne_arrayLengthSlot hprobe hold.2
    exact address_observation_effect raw entries target oldPauser index
      (mapSlot probe 3) (assignmentSlot probe)
      (hkeys.assignments probe hprobe)
      (solRegistryStorage_assignment raw probe hprobe).symm
      hmClean hpairM.2.1 hpairM.1 hlengthFam.1 hpairT.1
  · intro probe hprobe
    have hpair := registryAddressFamilies_pairwise
      htarget.2 hprobe hold.2
    have hnextWord : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega : index + 1 < 2 ^ 256)]
      omega
    have hlengthWord : (Nat.toB256 entries.length).toNat <
        2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega : entries.length < 2 ^ 256)]
      exact hlengthLt
    exact word_observation_effect raw entries target oldPauser index
      (mapSlot probe 4) (indexSlot probe)
      (hkeys.indices probe hprobe)
      (solRegistryStorage_index raw probe hprobe).symm
      hpair.1.symm
      (registryAddressFamilies_ne_arrayEntrySlot
        hprobe hold.2 hnextWord).2.1
      (registryAddressFamilies_ne_arrayEntrySlot
        hprobe hold.2 hlengthWord).2.1
  · intro probe hprobe
    have hpair := registryAddressFamilies_pairwise
      htarget.2 htarget.2 hprobe
    have hnextWord : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega : index + 1 < 2 ^ 256)]
      omega
    have hlengthWord : (Nat.toB256 entries.length).toNat <
        2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega : entries.length < 2 ^ 256)]
      exact hlengthLt
    exact word_observation_effect raw entries target oldPauser index
      (mapSlot probe 6) (countSlot probe)
      (hkeys.counts probe hprobe)
      (solRegistryStorage_count raw probe hprobe).symm
      hpair.2.1.symm
      (registryAddressFamilies_ne_arrayEntrySlot
        htarget.2 hprobe hnextWord).2.2
      (registryAddressFamilies_ne_arrayEntrySlot
        htarget.2 hprobe hlengthWord).2.2
  · have hlengthFam :=
      registryAddressFamilies_ne_arrayLengthSlot htarget.2 hold.2
    exact word_observation_effect raw entries target oldPauser index
      5 arrayLengthSlot hkeys.length
      (solRegistryStorage_length raw).symm
      hlengthFam.1.symm
      hholeLengthSep htailLengthSep
  · intro probe hprobe
    have hprobeLt : probe < entries.length := by omega
    have hword : (Nat.toB256 (probe + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega : probe + 1 < 2 ^ 256)]
      omega
    have hfamilies := registryAddressFamilies_ne_arrayEntrySlot
      hm.2 hold.2 hword
    have htargetFamily := registryAddressFamilies_ne_arrayEntrySlot
      htarget.2 hold.2 hword
    exact address_observation_effect raw entries target oldPauser index
      (registryArraySlot probe)
      (arrayEntrySlot (Nat.toB256 (probe + 1)))
      (hkeys.array probe hprobeLt)
      (solRegistryStorage_array raw probe (by omega)).symm
      hmClean hfamilies.2.2.symm hfamilies.2.1.symm
      (hw.arrayLengthSlot_ne_arrayEntrySlot hprobeLt).symm
      htargetFamily.2.1.symm

/-- The vacated tail's public address field is zero after the fifth write.
Only the two *later* writes must miss that physical slot; earlier aliases,
including the last-entry hole/tail alias, are harmless. -/
theorem rawRemovalPost_tail_address_zero (raw : Stor)
    (entries : List Entry) (target oldPauser : B256) (index : Nat)
    (hlength : registryArraySlot (entries.length - 1) ≠ 5)
    (hremoved : registryArraySlot (entries.length - 1) ≠
      mapSlot target 4) :
    addressSlotReadWord
      ((rawRemovalPost raw entries target oldPauser index).get
        (registryArraySlot (entries.length - 1))) = 0 := by
  unfold rawRemovalPost
  rw [Stor.get_set_ne _ (Ne.symm hremoved),
    Stor.get_set_ne _ (Ne.symm hlength), Stor.get_set_self]
  apply addressSlotReadWord_write_of_clean
  rfl

/-- Pointwise storage effects from a later bytecode run transport the same
tail-clear conclusion. The raw high 96 bits are intentionally unrestricted. -/
theorem rawRemoval_tail_address_zero
    {before after : Stor} {entries : List Entry}
    {target oldPauser : B256} {index : Nat}
    (hwrites : ∀ key, after.get key =
      (rawRemovalPost before entries target oldPauser index).get key)
    (hlength : registryArraySlot (entries.length - 1) ≠ 5)
    (hremoved : registryArraySlot (entries.length - 1) ≠
      mapSlot target 4) :
    addressSlotReadWord
      (after.get (registryArraySlot (entries.length - 1))) = 0 := by
  rw [hwrites]
  exact rawRemovalPost_tail_address_zero before entries target oldPauser index
    hlength hremoved

/-- A later execution proof needs only pointwise equality with the seven
stores; the local correspondences already discharge every read equation. -/
theorem rawRemovalReadEffect_of_local_keys_and_writes
    {before after : Stor} {entries : List Entry}
    {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage before) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hkeys : LocalRemovalKeys entries target oldPauser index)
    (hwrites : ∀ key, after.get key =
      (rawRemovalPost before entries target oldPauser index).get key) :
    RawRemovalReadEffect before after entries target oldPauser index := by
  let heffect := rawRemovalReadEffect_of_local_keys hw htarget hfind hkeys
  exact { heffect with writes := hwrites }

/-- Concrete application of the shared logical seven-write preservation
theorem to the deployed Solidity storage projection. -/
theorem rawRemoval_preservesRegistry
    {before after : Stor} {entries : List Entry}
    {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage before) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hkeys : LocalRemovalKeys entries target oldPauser index)
    (hwrites : ∀ key, after.get key =
      (rawRemovalPost before entries target oldPauser index).get key) :
    RegistryWitness (solRegistryStorage after) (swapPop entries index) := by
  exact RawRemovalReadEffect.preservesRegistry hw htarget hfind
    (rawRemovalReadEffect_of_local_keys_and_writes
      hw htarget hfind hkeys hwrites)

/-! ## `LocalRemovalKeys` is an instance of the unified premise

Everything above this point is unchanged.  `LocalRemovalKeys` remains the
proof-internal bundle `rawRemoval_preservesRegistry` consumes, but a caller
no longer has to state it directly: it is now *derived* from
`RegistryKeysFaithful`, the one premise shape §3 of the critique asked for
(`Blanc/Lift/LidoCircuitBreakerDeployed/RegistryLayout.lean`).  A future
bytecode-walk statement review reads one collision-freedom assumption for
every transition, not a bespoke bundle per transition. -/

/-- The seven logical keys `rawRemovalPost`'s writes touch, in write order:
exactly `removalLogicalKey`'s seven values.  `RegistryKeysFaithful` over this
list is what `LocalRemovalKeys` derives from. -/
def removalWriteKeys (entries : List Entry) (target oldPauser : B256)
    (index : Nat) : List B256 :=
  [assignmentSlot target, countSlot oldPauser,
    arrayEntrySlot (Nat.toB256 (index + 1)), indexSlot (sourceLastTarget entries),
    arrayEntrySlot (Nat.toB256 entries.length), arrayLengthSlot, indexSlot target]

private theorem removalRawKey_eq_solKey
    {raw : Stor} {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage raw) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (write : RemovalWrite) :
    removalRawKey entries target oldPauser index write =
      solKey (removalLogicalKey entries target oldPauser index write) := by
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hfoundLt := findEntry_index_lt hfind
  have hlengthLt := hw.entries_length_lt_2pow252
  obtain ⟨last, hlast⟩ := last_some_of_findEntry hfind
  have hlastValid : nonzeroCanonicalAddress last.1 :=
    hw.targetsValid last (last_mem_of_last entries hlast)
  have hm : nonzeroCanonicalAddress (sourceLastTarget entries) := by
    simpa [sourceLastTarget, hlast] using hlastValid
  cases write with
  | assignment => simp [removalRawKey, removalLogicalKey, solKey_assignmentSlot htarget.2]
  | count => simp [removalRawKey, removalLogicalKey, solKey_countSlot hold.2]
  | hole =>
    have hbound : index + 1 < 2 ^ 252 := by omega
    simp [removalRawKey, removalLogicalKey, solKey_arrayEntrySlot hbound]
  | movedIndex => simp [removalRawKey, removalLogicalKey, solKey_indexSlot hm.2]
  | tail =>
    have htailBound : entries.length - 1 + 1 < 2 ^ 252 := by omega
    have htailEq : entries.length - 1 + 1 = entries.length := by omega
    have h := solKey_arrayEntrySlot (index := entries.length - 1) htailBound
    rw [htailEq] at h
    simp only [removalRawKey, removalLogicalKey]
    exact h.symm
  | length => simp [removalRawKey, removalLogicalKey, solKey_arrayLengthSlot]
  | removedIndex => simp [removalRawKey, removalLogicalKey, solKey_indexSlot htarget.2]

/-- Every `LocalRemovalKeys` obligation is `RegistryKeysFaithful` read back at
the write whose raw/logical key pair it names. -/
theorem LocalRemovalKeys_of_registryKeysFaithful
    {raw : Stor} {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage raw) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : RegistryKeysFaithful entries.length
      (removalWriteKeys entries target oldPauser index)) :
    LocalRemovalKeys entries target oldPauser index := by
  have hcorr : ∀ {rawKey logicalKey : B256},
      RegistryObservable entries.length logicalKey → rawKey = solKey logicalKey →
      RemovalKeyCorrespondence entries target oldPauser index rawKey logicalKey := by
    intro rawKey logicalKey hobs hrawKey write
    have hrw := removalRawKey_eq_solKey hw htarget hfind write
    have hmem : removalLogicalKey entries target oldPauser index write ∈
        removalWriteKeys entries target oldPauser index := by
      cases write <;> simp [removalWriteKeys, removalLogicalKey]
    constructor
    · intro h
      apply hfaithful _ hmem logicalKey hobs
      rw [← hrawKey, h]
      exact hrw
    · intro h
      rw [hrawKey, h]
      exact hrw.symm
  have hlengthLt := hw.entries_length_lt_2pow252
  refine {
    assignments := fun probe hprobe =>
      hcorr (Or.inl ⟨probe, hprobe, rfl⟩) (solKey_assignmentSlot hprobe).symm
    indices := fun probe hprobe =>
      hcorr (Or.inr (Or.inl ⟨probe, hprobe, rfl⟩)) (solKey_indexSlot hprobe).symm
    counts := fun probe hprobe =>
      hcorr (Or.inr (Or.inr (Or.inl ⟨probe, hprobe, rfl⟩))) (solKey_countSlot hprobe).symm
    length :=
      hcorr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) solKey_arrayLengthSlot.symm
    array := fun probe hprobe => ?_ }
  have hbound : probe + 1 < 2 ^ 252 := by omega
  exact hcorr (Or.inr (Or.inr (Or.inr (Or.inr ⟨probe, hprobe, rfl⟩))))
    (solKey_arrayEntrySlot hbound).symm

/-- The raw seven-write pointwise effect, from the unified premise directly
(no `LocalRemovalKeys` to state). -/
theorem rawRemovalReadEffect_of_registryKeysFaithful
    {raw : Stor} {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage raw) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : RegistryKeysFaithful entries.length
      (removalWriteKeys entries target oldPauser index)) :
    RawRemovalReadEffect raw
      (rawRemovalPost raw entries target oldPauser index)
      entries target oldPauser index :=
  rawRemovalReadEffect_of_local_keys hw htarget hfind
    (LocalRemovalKeys_of_registryKeysFaithful hw htarget hfind hfaithful)

/-- `rawRemoval_preservesRegistry`, stated over the unified premise. -/
theorem rawRemoval_preservesRegistry_of_registryKeysFaithful
    {before after : Stor} {entries : List Entry} {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (solRegistryStorage before) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : RegistryKeysFaithful entries.length
      (removalWriteKeys entries target oldPauser index))
    (hwrites : ∀ key, after.get key =
      (rawRemovalPost before entries target oldPauser index).get key) :
    RegistryWitness (solRegistryStorage after) (swapPop entries index) :=
  RawRemovalReadEffect.preservesRegistry hw htarget hfind
    { rawRemovalReadEffect_of_registryKeysFaithful hw htarget hfind hfaithful with
      writes := hwrites }

end Blanc.Lift.LidoCircuitBreakerDeployed
