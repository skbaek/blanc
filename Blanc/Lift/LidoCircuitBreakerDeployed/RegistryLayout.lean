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

end Blanc.Lift.LidoCircuitBreakerDeployed
