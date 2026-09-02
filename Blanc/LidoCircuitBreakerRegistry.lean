import Blanc.LidoCircuitBreakerCode
import Blanc.ExecutionOccurrence
import Blanc.LidoCircuitBreakerRegistryModel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Chronological logical Registry writes for the shared CircuitBreaker kernel. -/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Ninst
open scoped BigOperators

/-- The logical Registry projection of concrete EVM storage. -/
def logicalStorageOfStor (s : Stor) : LogicalStorage := { read := s.get }

private theorem toB256_or (a b : Nat) :
    Nat.toB256 (a ||| b) =
      B256.or (Nat.toB256 a) (Nat.toB256 b) := by
  simp only [Nat.toB256, B256.or, Nat.shiftRight_or_distrib, toB128_or]

theorem slot_toNat_of_region_payload_lt
    {region : Nat} {payload : B256}
    (hregion : region < 16) (hpayload : payload.toNat < 2 ^ 252) :
    (slot region payload).toNat =
      region * 2 ^ 252 + payload.toNat := by
  have hdiv : 2 ^ 252 ∣ region * 2 ^ 252 := Nat.dvd_mul_left _ _
  have hor :
      region * 2 ^ 252 ||| payload.toNat =
        region * 2 ^ 252 + payload.toNat :=
    (Nat.add_eq_or hdiv hpayload).symm
  have hsum :
      region * 2 ^ 252 + payload.toNat < 2 ^ 256 := by
    calc
      region * 2 ^ 252 + payload.toNat <
          region * 2 ^ 252 + 2 ^ 252 :=
        Nat.add_lt_add_left hpayload _
      _ = (region + 1) * 2 ^ 252 := by omega
      _ ≤ 16 * 2 ^ 252 :=
        Nat.mul_le_mul_right (2 ^ 252) (Nat.succ_le_iff.mpr hregion)
      _ = 2 ^ 256 := by
        rw [show 256 = 4 + 252 by omega, pow_add]
        norm_num
  have horlt :
      region * 2 ^ 252 ||| payload.toNat < 2 ^ 256 := by
    rwa [hor]
  calc
    (slot region payload).toNat =
        (B256.or (Nat.toB256 (region * 2 ^ 252))
          (Nat.toB256 payload.toNat)).toNat := by
      rw [slot, regionWord, toB256_toNat]
    _ = (Nat.toB256
          (region * 2 ^ 252 ||| payload.toNat)).toNat := by
      rw [toB256_or]
    _ = region * 2 ^ 252 ||| payload.toNat :=
      B256.toNat_toB256_of_lt horlt
    _ = region * 2 ^ 252 + payload.toNat := hor

theorem slot_injective_payload
    {region : Nat} {left right : B256}
    (hregion : region < 16)
    (hleft : left.toNat < 2 ^ 252)
    (hright : right.toNat < 2 ^ 252)
    (hslot : slot region left = slot region right) :
    left = right := by
  apply B256.toNat_inj
  have hnat := congrArg B256.toNat hslot
  rw [slot_toNat_of_region_payload_lt hregion hleft,
    slot_toNat_of_region_payload_lt hregion hright] at hnat
  omega

theorem slot_ne_of_region_ne
    {leftRegion rightRegion : Nat} {left right : B256}
    (hlr : leftRegion < 16) (hrr : rightRegion < 16)
    (hleft : left.toNat < 2 ^ 252)
    (hright : right.toNat < 2 ^ 252)
    (hne : leftRegion ≠ rightRegion) :
    slot leftRegion left ≠ slot rightRegion right := by
  intro hslot
  apply hne
  have hnat := congrArg B256.toNat hslot
  rw [slot_toNat_of_region_payload_lt hlr hleft,
    slot_toNat_of_region_payload_lt hrr hright] at hnat
  omega

private def addressFin (word : B256) : Fin (2 ^ 160) :=
  ⟨word.toNat % (2 ^ 160), Nat.mod_lt _ (by norm_num)⟩

theorem RegistryWitness.entries_length_le
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) :
    entries.length ≤ 2 ^ 160 - 1 := by
  let targets := entries.map Prod.fst
  have hvalid :
      ∀ target ∈ targets, nonzeroCanonicalAddress target := by
    intro target htarget
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp htarget
    exact h.targetsValid entry hentry
  have hmapped : (targets.map addressFin).Nodup := by
    apply h.targetsNodup.map_on
    intro left hleft right hright heq
    apply B256.toNat_inj
    have hleftValid := hvalid left hleft
    have hrightValid := hvalid right hright
    have hleftLt : left.toNat < 2 ^ 160 := hleftValid.2
    have hrightLt : right.toNat < 2 ^ 160 := hrightValid.2
    have hval := congrArg Fin.val heq
    change left.toNat % (2 ^ 160) =
      right.toNat % (2 ^ 160) at hval
    rw [Nat.mod_eq_of_lt hleftLt, Nat.mod_eq_of_lt hrightLt] at hval
    exact hval
  have hzero : (0 : Fin (2 ^ 160)) ∉ targets.map addressFin := by
    intro hmem
    obtain ⟨target, htarget, heq⟩ := List.mem_map.mp hmem
    have htargetValid := hvalid target htarget
    have htargetLt : target.toNat < 2 ^ 160 := htargetValid.2
    apply htargetValid.1
    apply B256.toNat_inj
    have hval := congrArg Fin.val heq
    change target.toNat % (2 ^ 160) = 0 at hval
    rw [Nat.mod_eq_of_lt htargetLt] at hval
    simpa only [B256.toNat_zero] using hval
  have hcard :=
    (List.nodup_cons.mpr ⟨hzero, hmapped⟩).length_le_card
  simp only [List.length_cons, List.length_map, Fintype.card_fin] at hcard
  simp only [targets, List.length_map] at hcard
  omega

/-- A canonical address is small enough to be a tagged-slot payload. -/
theorem canonicalAddress_payload_lt {word : B256}
    (h : canonicalAddress word) : word.toNat < 2 ^ 252 := by
  unfold canonicalAddress at h
  norm_num at h ⊢
  omega

theorem RegistryWitness.entries_length_lt_2pow252
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) : entries.length < 2 ^ 252 := by
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.entries_length_lt_2pow256
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) : entries.length < 2 ^ 256 := by
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.fresh_length_lt_2pow252
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) : entries.length + 1 < 2 ^ 252 := by
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.fresh_length_lt_2pow256
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) : entries.length + 1 < 2 ^ 256 := by
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.oneBasedIndexAt_lt_2pow252
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) (target : B256) :
    oneBasedIndexAt entries target < 2 ^ 252 := by
  have hindex := oneBasedIndexAt_le_length entries target
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.assignmentCount_lt_2pow256
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) (pauser : B256) :
    assignmentCount entries pauser < 2 ^ 256 := by
  have hcount := assignmentCount_le_length entries pauser
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

/-- `Nat.toB256` is injective below the word modulus. -/
theorem natToB256_injective_of_lt {left right : Nat}
    (hleft : left < 2 ^ 256) (hright : right < 2 ^ 256)
    (h : Nat.toB256 left = Nat.toB256 right) : left = right := by
  have hnat := congrArg B256.toNat h
  simpa only [B256.toNat_toB256_of_lt hleft,
    B256.toNat_toB256_of_lt hright] using hnat

/-- Incrementing a bounded natural agrees with word addition by one. -/
theorem natToB256_succ_eq_add_one (n : Nat)
    (h : n + 1 < 2 ^ 256) :
    Nat.toB256 (n + 1) = Nat.toB256 n + 1 := by
  have hn : n < 2 ^ 256 := by omega
  have hnof : B256.Nof (Nat.toB256 n) 1 := by
    unfold B256.Nof
    rw [B256.toNat_toB256_of_lt hn]
    change n + 1 < 2 ^ 256
    exact h
  apply B256.toNat_inj
  rw [B256.toNat_toB256_of_lt h]
  rw [B256.toNat_add_eq_of_nof _ _ hnof]
  rw [B256.toNat_toB256_of_lt hn]
  rfl

/-- Decrementing a positive bounded natural agrees with word subtraction by
one. -/
theorem natToB256_pred_eq_sub_one (n : Nat)
    (hpos : 0 < n) (hlt : n < 2 ^ 256) :
    Nat.toB256 (n - 1) = Nat.toB256 n - 1 := by
  have hone : (1 : B256) ≤ Nat.toB256 n := by
    rw [B256.le_iff_toNat_le_toNat,
      B256.toNat_toB256_of_lt hlt]
    change 1 ≤ n
    omega
  apply B256.toNat_inj
  rw [B256.toNat_toB256_of_lt (by omega)]
  rw [B256.toNat_sub_eq_of_le _ _ hone]
  rw [B256.toNat_toB256_of_lt hlt]
  rfl

theorem RegistryWitness.freshLengthWord_eq_add_one
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) :
    Nat.toB256 (entries.length + 1) = Nat.toB256 entries.length + 1 :=
  natToB256_succ_eq_add_one entries.length h.fresh_length_lt_2pow256

theorem RegistryWitness.assignmentCountWord_succ_eq_add_one
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) (pauser : B256) :
    Nat.toB256 (assignmentCount entries pauser + 1) =
      Nat.toB256 (assignmentCount entries pauser) + 1 := by
  apply natToB256_succ_eq_add_one
  have hcount := assignmentCount_le_length entries pauser
  have hlength := h.entries_length_le
  norm_num at hlength ⊢
  omega

theorem RegistryWitness.assignmentCountWord_pred_eq_sub_one
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {target index pauser}
    (hfind : findEntry entries target = some (index, pauser)) :
    Nat.toB256 (assignmentCount entries pauser - 1) =
      Nat.toB256 (assignmentCount entries pauser) - 1 := by
  apply natToB256_pred_eq_sub_one
  · exact assignmentCount_pos_of_findEntry hfind
  · exact h.assignmentCount_lt_2pow256 pauser

/-- Two tagged address families with distinct regions cannot collide on
canonical payloads. -/
theorem addressSlots_ne_of_region_ne
    {leftRegion rightRegion : Nat} {left right : B256}
    (hlr : leftRegion < 16) (hrr : rightRegion < 16)
    (hleft : canonicalAddress left) (hright : canonicalAddress right)
    (hne : leftRegion ≠ rightRegion) :
    slot leftRegion left ≠ slot rightRegion right :=
  slot_ne_of_region_ne hlr hrr
    (canonicalAddress_payload_lt hleft)
    (canonicalAddress_payload_lt hright) hne

theorem addressSlot_injective
    {region : Nat} {left right : B256}
    (hregion : region < 16)
    (hleft : canonicalAddress left) (hright : canonicalAddress right)
    (hslot : slot region left = slot region right) : left = right :=
  slot_injective_payload hregion
    (canonicalAddress_payload_lt hleft)
    (canonicalAddress_payload_lt hright) hslot

theorem assignmentSlot_injective
    {left right : B256}
    (hleft : canonicalAddress left) (hright : canonicalAddress right)
    (hslot : assignmentSlot left = assignmentSlot right) : left = right := by
  exact addressSlot_injective (region := assignmentRegion)
    (by norm_num [assignmentRegion]) hleft hright
    (by simpa [assignmentSlot] using hslot)

theorem indexSlot_injective
    {left right : B256}
    (hleft : canonicalAddress left) (hright : canonicalAddress right)
    (hslot : indexSlot left = indexSlot right) : left = right := by
  exact addressSlot_injective (region := indexRegion)
    (by norm_num [indexRegion]) hleft hright
    (by simpa [indexSlot] using hslot)

theorem countSlot_injective
    {left right : B256}
    (hleft : canonicalAddress left) (hright : canonicalAddress right)
    (hslot : countSlot left = countSlot right) : left = right := by
  exact addressSlot_injective (region := countRegion)
    (by norm_num [countRegion]) hleft hright
    (by simpa [countSlot] using hslot)

theorem arrayEntrySlot_nat_injective_of_lt
    {left right : Nat}
    (hleft : left < 2 ^ 252) (hright : right < 2 ^ 252)
    (hslots : arrayEntrySlot (Nat.toB256 left) =
      arrayEntrySlot (Nat.toB256 right)) : left = right := by
  have hleft256 : left < 2 ^ 256 := by
    norm_num at hleft ⊢
    omega
  have hright256 : right < 2 ^ 256 := by
    norm_num at hright ⊢
    omega
  have hpayload : Nat.toB256 left = Nat.toB256 right :=
    slot_injective_payload (region := arrayRegion)
      (by norm_num [arrayRegion])
      (by simpa [B256.toNat_toB256_of_lt hleft256] using hleft)
      (by simpa [B256.toNat_toB256_of_lt hright256] using hright)
      (by simpa [arrayEntrySlot] using hslots)
  exact natToB256_injective_of_lt hleft256 hright256 hpayload

/-- Assignment, reverse-index, and count address families are pairwise
disjoint on canonical payloads. -/
theorem registryAddressFamilies_pairwise
    {assignmentTarget indexTarget countedPauser : B256}
    (hassignment : canonicalAddress assignmentTarget)
    (hindex : canonicalAddress indexTarget)
    (hcount : canonicalAddress countedPauser) :
    assignmentSlot assignmentTarget ≠ indexSlot indexTarget ∧
    assignmentSlot assignmentTarget ≠ countSlot countedPauser ∧
    indexSlot indexTarget ≠ countSlot countedPauser := by
  constructor
  · simpa [assignmentSlot, indexSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := assignmentRegion) (rightRegion := indexRegion)
        (by norm_num [assignmentRegion]) (by norm_num [indexRegion])
        hassignment hindex (by norm_num [assignmentRegion, indexRegion])
  constructor
  · simpa [assignmentSlot, countSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := assignmentRegion) (rightRegion := countRegion)
        (by norm_num [assignmentRegion]) (by norm_num [countRegion])
        hassignment hcount (by norm_num [assignmentRegion, countRegion])
  · simpa [indexSlot, countSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := indexRegion) (rightRegion := countRegion)
        (by norm_num [indexRegion]) (by norm_num [countRegion])
        hindex hcount (by norm_num [indexRegion, countRegion])

/-- The expiry family is disjoint from all address-keyed Registry families. -/
theorem expirySlot_ne_registryAddressFamilies
    {expiryPauser target countedPauser : B256}
    (hexpiry : canonicalAddress expiryPauser)
    (htarget : canonicalAddress target)
    (hcount : canonicalAddress countedPauser) :
    expirySlot expiryPauser ≠ assignmentSlot target ∧
    expirySlot expiryPauser ≠ indexSlot target ∧
    expirySlot expiryPauser ≠ countSlot countedPauser := by
  constructor
  · simpa [expirySlot, assignmentSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := expiryRegion) (rightRegion := assignmentRegion)
        (by norm_num [expiryRegion]) (by norm_num [assignmentRegion])
        hexpiry htarget (by norm_num [expiryRegion, assignmentRegion])
  constructor
  · simpa [expirySlot, indexSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := expiryRegion) (rightRegion := indexRegion)
        (by norm_num [expiryRegion]) (by norm_num [indexRegion])
        hexpiry htarget (by norm_num [expiryRegion, indexRegion])
  · simpa [expirySlot, countSlot] using
      addressSlots_ne_of_region_ne
        (leftRegion := expiryRegion) (rightRegion := countRegion)
        (by norm_num [expiryRegion]) (by norm_num [countRegion])
        hexpiry hcount (by norm_num [expiryRegion, countRegion])

/-- Address-keyed Registry families are disjoint from every bounded array
entry key. -/
theorem registryAddressFamilies_ne_arrayEntrySlot
    {target pauser oneBasedIndex : B256}
    (htarget : canonicalAddress target)
    (hpauser : canonicalAddress pauser)
    (hindex : oneBasedIndex.toNat < 2 ^ 252) :
    assignmentSlot target ≠ arrayEntrySlot oneBasedIndex ∧
    indexSlot target ≠ arrayEntrySlot oneBasedIndex ∧
    countSlot pauser ≠ arrayEntrySlot oneBasedIndex := by
  constructor
  · simpa [assignmentSlot, arrayEntrySlot] using
      slot_ne_of_region_ne
        (leftRegion := assignmentRegion) (rightRegion := arrayRegion)
        (by norm_num [assignmentRegion]) (by norm_num [arrayRegion])
        (canonicalAddress_payload_lt htarget) hindex
        (by norm_num [assignmentRegion, arrayRegion])
  constructor
  · simpa [indexSlot, arrayEntrySlot] using
      slot_ne_of_region_ne
        (leftRegion := indexRegion) (rightRegion := arrayRegion)
        (by norm_num [indexRegion]) (by norm_num [arrayRegion])
        (canonicalAddress_payload_lt htarget) hindex
        (by norm_num [indexRegion, arrayRegion])
  · simpa [countSlot, arrayEntrySlot] using
      slot_ne_of_region_ne
        (leftRegion := countRegion) (rightRegion := arrayRegion)
        (by norm_num [countRegion]) (by norm_num [arrayRegion])
        (canonicalAddress_payload_lt hpauser) hindex
        (by norm_num [countRegion, arrayRegion])

theorem registryAddressFamilies_ne_arrayLengthSlot
    {target pauser : B256}
    (htarget : canonicalAddress target)
    (hpauser : canonicalAddress pauser) :
    assignmentSlot target ≠ arrayLengthSlot ∧
    indexSlot target ≠ arrayLengthSlot ∧
    countSlot pauser ≠ arrayLengthSlot := by
  have h := registryAddressFamilies_ne_arrayEntrySlot
    (oneBasedIndex := (0 : B256)) htarget hpauser
    (by
      change (0 : Nat) < 2 ^ 252
      norm_num)
  simpa [arrayEntrySlot, arrayLengthSlot] using h

/-- The expiry family is disjoint from the array length and every bounded
array-entry key. -/
theorem expirySlot_ne_arrayFamily
    {pauser oneBasedIndex : B256}
    (hpauser : canonicalAddress pauser)
    (hindex : oneBasedIndex.toNat < 2 ^ 252) :
    expirySlot pauser ≠ arrayLengthSlot ∧
    expirySlot pauser ≠ arrayEntrySlot oneBasedIndex := by
  constructor
  · simpa [expirySlot, arrayLengthSlot] using
      slot_ne_of_region_ne
        (leftRegion := expiryRegion) (rightRegion := arrayRegion)
        (by norm_num [expiryRegion]) (by norm_num [arrayRegion])
        (canonicalAddress_payload_lt hpauser)
        (by
          change (0 : Nat) < 2 ^ 252
          norm_num)
        (by norm_num [expiryRegion, arrayRegion])
  · simpa [expirySlot, arrayEntrySlot] using
      slot_ne_of_region_ne
        (leftRegion := expiryRegion) (rightRegion := arrayRegion)
        (by norm_num [expiryRegion]) (by norm_num [arrayRegion])
        (canonicalAddress_payload_lt hpauser) hindex
        (by norm_num [expiryRegion, arrayRegion])

/-- Writing one canonical pauser's expiry cannot alter any projected Registry
field. -/
theorem RegistryWitness.expiry_set
    {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    {pauser value : B256}
    (hpauser : canonicalAddress pauser) :
    RegistryWitness
      (logicalStorageOfStor (s.set (expirySlot pauser) value)) entries := by
  refine {
    targetsNodup := hw.targetsNodup
    targetsValid := hw.targetsValid
    pausersValid := hw.pausersValid
    lengthWord := ?_
    arrayWords := ?_
    assignments := ?_
    indices := ?_
    counts := ?_
    zeroCount := ?_
  }
  · have h := expirySlot_ne_arrayFamily (pauser := pauser)
      (oneBasedIndex := (0 : B256)) hpauser (by
        change (0 : Nat) < 2 ^ 252
        norm_num)
    change (s.set (expirySlot pauser) value).get arrayLengthSlot =
      Nat.toB256 entries.length
    rw [Stor.get_set_ne _ h.1]
    exact hw.lengthWord
  · intro index hindex
    have hindex256 : index + 1 < 2 ^ 256 := by
      have hbound := hw.entries_length_le
      norm_num at hbound ⊢
      omega
    have hindex252 :
        (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt hindex256]
      have hbound := hw.entries_length_le
      norm_num at hbound ⊢
      omega
    have h := expirySlot_ne_arrayFamily hpauser hindex252
    change (s.set (expirySlot pauser) value).get
      (arrayEntrySlot (Nat.toB256 (index + 1))) = targetAt entries index
    rw [Stor.get_set_ne _ h.2]
    exact hw.arrayWords index hindex
  · intro target htarget
    have h := expirySlot_ne_registryAddressFamilies hpauser htarget htarget
    change (s.set (expirySlot pauser) value).get (assignmentSlot target) =
      assignmentAt entries target
    rw [Stor.get_set_ne _ h.1]
    exact hw.assignments target htarget
  · intro target htarget
    have h := expirySlot_ne_registryAddressFamilies hpauser htarget htarget
    change (s.set (expirySlot pauser) value).get (indexSlot target) =
      Nat.toB256 (oneBasedIndexAt entries target)
    rw [Stor.get_set_ne _ h.2.1]
    exact hw.indices target htarget
  · intro counted hcounted
    have h := expirySlot_ne_registryAddressFamilies hpauser hcounted hcounted
    change (s.set (expirySlot pauser) value).get (countSlot counted) =
      Nat.toB256 (assignmentCount entries counted)
    rw [Stor.get_set_ne _ h.2.2]
    exact hw.counts counted hcounted
  · have hzero : canonicalAddress (0 : B256) := by
      unfold canonicalAddress
      change (0 : Nat) < 2 ^ 160
      norm_num
    have h := expirySlot_ne_registryAddressFamilies hpauser hzero hzero
    change (s.set (expirySlot pauser) value).get (countSlot 0) = 0
    rw [Stor.get_set_ne _ h.2.2]
    exact hw.zeroCount

/-- A write ending before a requested slice leaves that later slice unchanged. -/
private theorem Bytes.sliceD_writeAt_after
    (bs xs : Bytes) (start len n : Nat)
    (h : n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt]
  rw [if_neg]
  omega

/-- The three removal scratch writes occur strictly after the caller words. -/
private theorem removeImage_sliceD
    (img : Bytes) (start len : Nat)
    (indexWord lengthWord lastTarget : B256)
    (hremoved : start + len ≤ (removedIndexWord * 32).toNat)
    (hlength : start + len ≤ (arrayLengthWord * 32).toNat)
    (hlast : start + len ≤ (lastTargetWord * 32).toNat) :
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt img (removedIndexWord * 32).toNat
          indexWord.toBytes)
        (arrayLengthWord * 32).toNat lengthWord.toBytes)
      (lastTargetWord * 32).toNat lastTarget.toBytes).sliceD
        start len 0 = img.sliceD start len 0 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlast]
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hlength]
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hremoved]

/-- The array length key is distinct from every nonzero bounded array key. -/
theorem arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt
    {oneBasedIndex : B256} (hpos : oneBasedIndex ≠ 0)
    (hindex : oneBasedIndex.toNat < 2 ^ 252) :
    arrayLengthSlot ≠ arrayEntrySlot oneBasedIndex := by
  intro h
  have hpayload : (0 : B256) = oneBasedIndex :=
    slot_injective_payload (region := arrayRegion)
      (left := 0) (right := oneBasedIndex)
      (by norm_num [arrayRegion])
      (by
        change (0 : Nat) < 2 ^ 252
        norm_num)
      hindex
      (by simpa [arrayLengthSlot, arrayEntrySlot] using h)
  exact hpos hpayload.symm

theorem RegistryWitness.arrayLengthSlot_ne_arrayEntrySlot
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {index : Nat}
    (hindex : index < entries.length) :
    arrayLengthSlot ≠ arrayEntrySlot (Nat.toB256 (index + 1)) := by
  have hbound256 : index + 1 < 2 ^ 256 := by
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  apply arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt
  · intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hbound256] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  · rw [B256.toNat_toB256_of_lt hbound256]
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega

theorem RegistryWitness.arrayEntrySlot_injective
    {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) {left right : Nat}
    (hleft : left < entries.length) (hright : right < entries.length)
    (hslots : arrayEntrySlot (Nat.toB256 (left + 1)) =
      arrayEntrySlot (Nat.toB256 (right + 1))) : left = right := by
  have hleft256 : left + 1 < 2 ^ 256 := by
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  have hright256 : right + 1 < 2 ^ 256 := by
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  have hleft252 : (Nat.toB256 (left + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hleft256]
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  have hright252 : (Nat.toB256 (right + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hright256]
    have hlength := h.entries_length_le
    norm_num at hlength ⊢
    omega
  have hpayload : Nat.toB256 (left + 1) = Nat.toB256 (right + 1) :=
    slot_injective_payload (region := arrayRegion)
      (by norm_num [arrayRegion]) hleft252 hright252
      (by simpa [arrayEntrySlot] using hslots)
  exact Nat.add_right_cancel
    (natToB256_injective_of_lt hleft256 hright256 hpayload)

/-- One Registry SSTORE, represented as its key and new value. -/
abbrev RegistryWrite := B256 × B256

/-- Apply Registry SSTOREs in their execution order. -/
def applyRegistryWrites (s : Stor) (writes : List RegistryWrite) : Stor :=
  writes.foldl (fun storage write => storage.set write.1 write.2) s

/-- Pointwise read semantics of chronological Registry writes.  Repeated keys
remain ordered; each matching write replaces the current cell value. -/
theorem applyRegistryWrites_get (s : Stor) (writes : List RegistryWrite)
    (key : B256) :
    (applyRegistryWrites s writes).get key =
      writes.foldl
        (fun current write => if write.1 = key then write.2 else current)
        (s.get key) := by
  unfold applyRegistryWrites
  induction writes generalizing s with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      by_cases h : write.1 = key
      · rw [if_pos h, ← h, Stor.get_set_self]
      · rw [if_neg h, Stor.get_set_ne s h write.2]

private theorem mem_of_findEntry {entries : List Entry} {target : B256}
    {index : Nat} {pauser : B256}
    (h : findEntry entries target = some (index, pauser)) :
    (target, pauser) ∈ entries := by
  induction entries generalizing index pauser with
  | nil => simp [findEntry] at h
  | cons entry rest ih =>
      by_cases heq : entry.1 = target
      · simp [findEntry, heq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [← heq]
      · cases hrest : findEntry rest target with
        | none => simp [findEntry, heq, hrest] at h
        | some found =>
            obtain ⟨foundIndex, foundPauser⟩ := found
            simp [findEntry, heq, hrest] at h
            obtain ⟨rfl, rfl⟩ := h
            exact List.mem_cons_of_mem entry (ih hrest)

/-- A concrete Registry witness makes every current assignment canonical,
including the zero value of an absent target. -/
theorem RegistryWitness.assignmentAt_canonical
    {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (target : B256) :
    canonicalAddress (assignmentAt entries target) := by
  cases hfind : findEntry entries target with
  | none =>
      rw [findEntry_none_assignmentAt hfind]
      unfold canonicalAddress
      change (0 : Nat) < 2 ^ 160
      norm_num
  | some found =>
      obtain ⟨index, pauser⟩ := found
      have hmem : (target, pauser) ∈ entries := mem_of_findEntry hfind
      rw [findEntry_assignmentAt hfind]
      exact (hw.pausersValid (target, pauser) hmem).2

/-- A fresh nonzero registration's exact five writes restore the combined
Registry witness at the post-Registry boundary. -/
theorem RegistryWitness.applyFreshWrites
    {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    {target newPauser : B256}
    (htarget : nonzeroCanonicalAddress target)
    (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = none) :
    RegistryWitness
      (logicalStorageOfStor
        (applyRegistryWrites s
          [(assignmentSlot target, newPauser),
            (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
            (indexSlot target, Nat.toB256 (entries.length + 1)),
            (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
            (countSlot newPauser,
              Nat.toB256 (assignmentCount entries newPauser + 1))]))
      (entries ++ [(target, newPauser)]) := by
  have hnext256 := hw.fresh_length_lt_2pow256
  have hnext252 :
      (Nat.toB256 (entries.length + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hnext256]
    exact hw.fresh_length_lt_2pow252
  have hnext0 : Nat.toB256 (entries.length + 1) ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hnext256] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  have hlengthNext :=
    arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnext0 hnext252
  have haddressLength :=
    registryAddressFamilies_ne_arrayLengthSlot htarget.2 hnew.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨hw.targetsNodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro heq
    apply findEntry_none_target_not_mem_targets hfind
    rw [← heq]
    exact ha
  · intro entry hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact hw.targetsValid entry hmem
    · exact htarget
  · intro entry hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact hw.pausersValid entry hmem
    · exact hnew
  · simp only [logicalStorageOfStor, applyRegistryWrites_get,
      List.foldl_cons, List.foldl_nil]
    simp [haddressLength.2.2]
  · intro index hindex
    by_cases hold : index < entries.length
    · have hold256 : index + 1 < 2 ^ 256 := by
        have hlength := hw.entries_length_le
        norm_num at hlength ⊢
        omega
      have hold252 : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
        rw [B256.toNat_toB256_of_lt hold256]
        have hlength := hw.entries_length_le
        norm_num at hlength ⊢
        omega
      have hfamilies :=
        registryAddressFamilies_ne_arrayEntrySlot
          htarget.2 hnew.2 hold252
      have hlengthOld := hw.arrayLengthSlot_ne_arrayEntrySlot hold
      have hnewOld : arrayEntrySlot (Nat.toB256 (entries.length + 1)) ≠
          arrayEntrySlot (Nat.toB256 (index + 1)) := by
        intro heq
        have heqNat := arrayEntrySlot_nat_injective_of_lt
          hw.fresh_length_lt_2pow252
          (by
            have hlength := hw.entries_length_le
            norm_num at hlength ⊢
            omega) heq
        omega
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hfamilies.1, hfamilies.2.1, hfamilies.2.2,
        hnewOld, hlengthOld,
        targetAt_append_old entries (target, newPauser) hold]
      simpa [logicalStorageOfStor] using hw.arrayWords index hold
    · have heq : index = entries.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hindex
        omega
      subst index
      have hfamilies :=
        registryAddressFamilies_ne_arrayEntrySlot
          htarget.2 hnew.2 hnext252
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hfamilies.2.1, hfamilies.2.2,
        hlengthNext,
        targetAt_append_length_of_findEntry_none hfind]
  · intro wanted hwanted
    have hpair :=
      registryAddressFamilies_pairwise hwanted htarget.2 hnew.2
    have harray :=
      registryAddressFamilies_ne_arrayEntrySlot hwanted hnew.2 hnext252
    have hlength :=
      registryAddressFamilies_ne_arrayLengthSlot hwanted hnew.2
    by_cases heq : wanted = target
    · subst wanted
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [Ne.symm harray.1, Ne.symm hpair.1,
        Ne.symm hlength.1, Ne.symm hpair.2.1,
        assignmentAt_append_target_of_findEntry_none hfind]
    · have hassignment : assignmentSlot target ≠ assignmentSlot wanted := by
        intro hslots
        exact (Ne.symm heq)
          (assignmentSlot_injective htarget.2 hwanted hslots)
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hassignment, Ne.symm harray.1, Ne.symm hpair.1,
        Ne.symm hlength.1, Ne.symm hpair.2.1,
        assignmentAt_append_of_ne entries target newPauser wanted heq]
      simpa [logicalStorageOfStor] using hw.assignments wanted hwanted
  · intro wanted hwanted
    have hpair :=
      registryAddressFamilies_pairwise htarget.2 hwanted hnew.2
    have harray :=
      registryAddressFamilies_ne_arrayEntrySlot hwanted hnew.2 hnext252
    have hlength :=
      registryAddressFamilies_ne_arrayLengthSlot hwanted hnew.2
    by_cases heq : wanted = target
    · subst wanted
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [Ne.symm hpair.2.2,
        oneBasedIndexAt_append_target_of_findEntry_none hfind]
    · have hindexSlot : indexSlot target ≠ indexSlot wanted := by
        intro hslots
        exact (Ne.symm heq) (indexSlot_injective htarget.2 hwanted hslots)
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hpair.1, Ne.symm harray.2.1, hindexSlot,
        Ne.symm hlength.2.1, Ne.symm hpair.2.2,
        oneBasedIndexAt_append_of_ne entries target newPauser wanted heq]
      simpa [logicalStorageOfStor] using hw.indices wanted hwanted
  · intro wanted hwanted
    have hpair :=
      registryAddressFamilies_pairwise htarget.2 htarget.2 hwanted
    have harray :=
      registryAddressFamilies_ne_arrayEntrySlot htarget.2 hwanted hnext252
    have hlength :=
      registryAddressFamilies_ne_arrayLengthSlot htarget.2 hwanted
    by_cases heq : wanted = newPauser
    · subst wanted
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [assignmentCount_append, Nat.add_comm]
    · have hcountSlot : countSlot newPauser ≠ countSlot wanted := by
        intro hslots
        exact (Ne.symm heq) (countSlot_injective hnew.2 hwanted hslots)
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hpair.2.1, Ne.symm harray.2.2, hpair.2.2,
        Ne.symm hlength.2.2, hcountSlot, assignmentCount_append,
        if_neg (Ne.symm heq)]
      simpa [logicalStorageOfStor] using hw.counts wanted hwanted
  · have hzeroCanonical : canonicalAddress (0 : B256) := by
      unfold canonicalAddress
      change (0 : Nat) < 2 ^ 160
      norm_num
    have hpair :=
      registryAddressFamilies_pairwise htarget.2 htarget.2 hzeroCanonical
    have harray :=
      registryAddressFamilies_ne_arrayEntrySlot
        htarget.2 hzeroCanonical hnext252
    have hlength :=
      registryAddressFamilies_ne_arrayLengthSlot
        htarget.2 hzeroCanonical
    have hcount0 : countSlot newPauser ≠ countSlot 0 := by
      intro hslots
      exact hnew.1 (countSlot_injective hnew.2 hzeroCanonical hslots)
    simp only [logicalStorageOfStor, applyRegistryWrites_get,
      List.foldl_cons, List.foldl_nil]
    simp [hpair.2.1, Ne.symm harray.2.2, hpair.2.2,
      Ne.symm hlength.2.2, hcount0]
    simpa [logicalStorageOfStor] using hw.zeroCount

/-- Reassigning an existing target to a nonzero pauser preserves the combined
Registry witness after the exact assignment, decrement, and increment chronology. -/
theorem RegistryWitness.applyFoundNonzeroWrites
    {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    {target newPauser oldPauser : B256} {index : Nat}
    (htarget : nonzeroCanonicalAddress target)
    (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = some (index, oldPauser)) :
    RegistryWitness
      (logicalStorageOfStor
        (applyRegistryWrites s
          [(assignmentSlot target, newPauser),
            (countSlot oldPauser,
              Nat.toB256 (assignmentCount entries oldPauser - 1)),
            (countSlot newPauser,
              Nat.toB256
                ((assignmentCount entries newPauser -
                  (if oldPauser = newPauser then 1 else 0)) + 1))]))
      (setEntryAt index (target, newPauser) entries) := by
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [setEntryAt_targets_of_findEntry hfind]
    exact hw.targetsNodup
  · exact setEntryAt_targetsValid_of_findEntry hfind hw.targetsValid
  · exact setEntryAt_pausersValid_of_findEntry hfind hw.pausersValid hnew
  · have holdLength :=
      registryAddressFamilies_ne_arrayLengthSlot htarget.2 hold.2
    have hnewLength :=
      registryAddressFamilies_ne_arrayLengthSlot htarget.2 hnew.2
    simp only [logicalStorageOfStor, applyRegistryWrites_get,
      List.foldl_cons, List.foldl_nil]
    simp [holdLength.1, holdLength.2.2, hnewLength.2.2,
      setEntryAt_length_of_findEntry hfind]
    simpa [logicalStorageOfStor] using hw.lengthWord
  · intro wantedIndex hwantedIndex
    have holdIndex : wantedIndex < entries.length := by
      rw [setEntryAt_length_of_findEntry hfind] at hwantedIndex
      exact hwantedIndex
    have hword256 : wantedIndex + 1 < 2 ^ 256 := by
      have hlength := hw.entries_length_le
      norm_num at hlength ⊢
      omega
    have hword252 :
        (Nat.toB256 (wantedIndex + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt hword256]
      have hlength := hw.entries_length_le
      norm_num at hlength ⊢
      omega
    have holdArray :=
      registryAddressFamilies_ne_arrayEntrySlot htarget.2 hold.2 hword252
    have hnewArray :=
      registryAddressFamilies_ne_arrayEntrySlot htarget.2 hnew.2 hword252
    simp only [logicalStorageOfStor, applyRegistryWrites_get,
      List.foldl_cons, List.foldl_nil]
    simp [holdArray.1, holdArray.2.2, hnewArray.2.2,
      targetAt_setEntryAt_of_findEntry hfind holdIndex]
    simpa [logicalStorageOfStor] using hw.arrayWords wantedIndex holdIndex
  · intro wanted hwanted
    have holdPair :=
      registryAddressFamilies_pairwise hwanted htarget.2 hold.2
    have hnewPair :=
      registryAddressFamilies_pairwise hwanted htarget.2 hnew.2
    by_cases heq : wanted = target
    · subst wanted
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [Ne.symm holdPair.2.1, Ne.symm hnewPair.2.1,
        assignmentAt_setEntryAt_target_of_findEntry hfind]
    · have hassignment : assignmentSlot target ≠ assignmentSlot wanted := by
        intro hslots
        exact (Ne.symm heq)
          (assignmentSlot_injective htarget.2 hwanted hslots)
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hassignment, Ne.symm holdPair.2.1, Ne.symm hnewPair.2.1,
        assignmentAt_setEntryAt_of_findEntry_ne hfind heq]
      simpa [logicalStorageOfStor] using hw.assignments wanted hwanted
  · intro wanted hwanted
    have holdPair :=
      registryAddressFamilies_pairwise htarget.2 hwanted hold.2
    have hnewPair :=
      registryAddressFamilies_pairwise htarget.2 hwanted hnew.2
    simp only [logicalStorageOfStor, applyRegistryWrites_get,
      List.foldl_cons, List.foldl_nil]
    simp [holdPair.1, Ne.symm holdPair.2.2, Ne.symm hnewPair.2.2,
      oneBasedIndexAt_setEntryAt_of_findEntry hfind]
    simpa [logicalStorageOfStor] using hw.indices wanted hwanted
  · intro wanted hwanted
    have hassignment :=
      registryAddressFamilies_pairwise htarget.2 htarget.2 hwanted
    by_cases hnewEq : wanted = newPauser
    · subst wanted
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [assignmentCount_setEntryAt_of_findEntry hfind]
    · have hcountNew : countSlot newPauser ≠ countSlot wanted := by
        intro hslots
        exact (Ne.symm hnewEq)
          (countSlot_injective hnew.2 hwanted hslots)
      by_cases holdEq : wanted = oldPauser
      · subst wanted
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [hcountNew, Ne.symm hnewEq,
          assignmentCount_setEntryAt_of_findEntry hfind]
      · have hcountOld : countSlot oldPauser ≠ countSlot wanted := by
          intro hslots
          exact (Ne.symm holdEq)
            (countSlot_injective hold.2 hwanted hslots)
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [hassignment.2.1, hcountOld, hcountNew]
        rw [assignmentCount_setEntryAt_of_findEntry hfind]
        simp [Ne.symm holdEq, Ne.symm hnewEq]
        simpa [logicalStorageOfStor] using hw.counts wanted hwanted
  · have hzeroCanonical : canonicalAddress (0 : B256) := by
      unfold canonicalAddress
      change (0 : Nat) < 2 ^ 160
      norm_num
    have hassignment :=
      registryAddressFamilies_pairwise htarget.2 htarget.2 hzeroCanonical
    have hold0 : countSlot oldPauser ≠ countSlot 0 := by
      intro hslots
      exact hold.1 (countSlot_injective hold.2 hzeroCanonical hslots)
    have hnew0 : countSlot newPauser ≠ countSlot 0 := by
      intro hslots
      exact hnew.1 (countSlot_injective hnew.2 hzeroCanonical hslots)
    simp only [logicalStorageOfStor, applyRegistryWrites_get,
      List.foldl_cons, List.foldl_nil]
    simp [hassignment.2.1, hold0, hnew0]
    simpa [logicalStorageOfStor] using hw.zeroCount

/-- The absent-target/zero-pauser path restores the original witness after its
exact append, repeated-write, tail-clear, length-restore, and index-clear trace. -/
theorem RegistryWitness.applyAbsentZeroWrites
    {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    {target : B256}
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = none) :
    RegistryWitness
      (logicalStorageOfStor
        (applyRegistryWrites s
          [(assignmentSlot target, 0),
            (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
            (indexSlot target, Nat.toB256 (entries.length + 1)),
            (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
            (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
            (indexSlot target, Nat.toB256 (entries.length + 1)),
            (arrayEntrySlot (Nat.toB256 (entries.length + 1)), 0),
            (arrayLengthSlot, Nat.toB256 entries.length),
            (indexSlot target, 0)]))
      entries := by
  have hnext256 := hw.fresh_length_lt_2pow256
  have hnext252 :
      (Nat.toB256 (entries.length + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hnext256]
    exact hw.fresh_length_lt_2pow252
  have hnext0 : Nat.toB256 (entries.length + 1) ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hnext256] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  have hlengthNext :=
    arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnext0 hnext252
  exact {
    targetsNodup := hw.targetsNodup
    targetsValid := hw.targetsValid
    pausersValid := hw.pausersValid
    lengthWord := by
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot htarget.2 htarget.2
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hlength.2.1]
    arrayWords := by
      intro index hindex
      have hold256 : index + 1 < 2 ^ 256 := by
        have hbound := hw.entries_length_le
        norm_num at hbound ⊢
        omega
      have hold252 : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
        rw [B256.toNat_toB256_of_lt hold256]
        have hbound := hw.entries_length_le
        norm_num at hbound ⊢
        omega
      have hfamilies :=
        registryAddressFamilies_ne_arrayEntrySlot
          htarget.2 htarget.2 hold252
      have holdLength := hw.arrayLengthSlot_ne_arrayEntrySlot hindex
      have hfreshOld :
          arrayEntrySlot (Nat.toB256 (entries.length + 1)) ≠
            arrayEntrySlot (Nat.toB256 (index + 1)) := by
        intro heq
        have heqNat := arrayEntrySlot_nat_injective_of_lt
          hw.fresh_length_lt_2pow252
          (by
            have hbound := hw.entries_length_le
            norm_num at hbound ⊢
            omega) heq
        omega
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hfamilies.1, hfamilies.2.1, hfreshOld, holdLength]
      simpa [logicalStorageOfStor] using hw.arrayWords index hindex
    assignments := by
      intro wanted hwanted
      have harray :=
        registryAddressFamilies_ne_arrayEntrySlot hwanted htarget.2 hnext252
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot hwanted htarget.2
      have hpair :=
        registryAddressFamilies_pairwise hwanted htarget.2 htarget.2
      by_cases heq : wanted = target
      · subst wanted
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [Ne.symm harray.1, Ne.symm hpair.1, Ne.symm hlength.1,
          findEntry_none_assignmentAt hfind]
      · have hassignment : assignmentSlot target ≠ assignmentSlot wanted := by
          intro hslots
          exact (Ne.symm heq)
            (assignmentSlot_injective htarget.2 hwanted hslots)
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [hassignment, Ne.symm harray.1, Ne.symm hpair.1,
          Ne.symm hlength.1]
        simpa [logicalStorageOfStor] using hw.assignments wanted hwanted
    indices := by
      intro wanted hwanted
      have harray :=
        registryAddressFamilies_ne_arrayEntrySlot hwanted hwanted hnext252
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot hwanted hwanted
      have hpair :=
        registryAddressFamilies_pairwise htarget.2 hwanted htarget.2
      by_cases heq : wanted = target
      · subst wanted
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        (simp [findEntry_none_oneBasedIndexAt hfind]; rfl)
      · have hindexSlot : indexSlot target ≠ indexSlot wanted := by
          intro hslots
          exact (Ne.symm heq)
            (indexSlot_injective htarget.2 hwanted hslots)
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [hpair.1, Ne.symm harray.2.1, hindexSlot,
          Ne.symm hlength.2.1]
        simpa [logicalStorageOfStor] using hw.indices wanted hwanted
    counts := by
      intro wanted hwanted
      have harray :=
        registryAddressFamilies_ne_arrayEntrySlot htarget.2 hwanted hnext252
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot htarget.2 hwanted
      have hpair :=
        registryAddressFamilies_pairwise htarget.2 htarget.2 hwanted
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hpair.2.1, hpair.2.2, Ne.symm harray.2.2,
        Ne.symm hlength.2.2]
      simpa [logicalStorageOfStor] using hw.counts wanted hwanted
    zeroCount := by
      have hzeroCanonical : canonicalAddress (0 : B256) := by
        unfold canonicalAddress
        change (0 : Nat) < 2 ^ 160
        norm_num
      have harray :=
        registryAddressFamilies_ne_arrayEntrySlot
          htarget.2 hzeroCanonical hnext252
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot htarget.2 hzeroCanonical
      have hpair :=
        registryAddressFamilies_pairwise htarget.2 htarget.2 hzeroCanonical
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hpair.2.1, hpair.2.2, Ne.symm harray.2.2,
        Ne.symm hlength.2.2]
      simpa [logicalStorageOfStor] using hw.zeroCount
  }

/-- The target in the current final array entry, if any.  A found source target
ensures this is the real final target; the zero default only defines the
otherwise-unreachable empty case. -/
def sourceLastTarget (entries : List Entry) : B256 :=
  match last? entries with
  | none => 0
  | some entry => entry.1

private theorem prefix_of_loadWord_image
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
      Devm.getStor pre = Devm.getStor post := by
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
  refine ⟨hp2, ?_, ?_, ?_⟩
  · rw [hm2]
    exact hwf1.extend _ _
  · rw [hm2]
    exact Mem.Reads.extend hr1 _ _
  · exact Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2 Line.Run.nil))

private theorem of_run_mstoreAt_image
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {img : Bytes} {word value : B256}
    (hp : value :: xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (run : Line.Run sevm pre (mstoreAt word) post) :
    xs <<+ post.stack ∧ Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt img (word * 32).toNat value.toBytes) ∧
      Devm.getStor pre = Devm.getStor post := by
  rcases of_run_mstoreAt_val run hp with ⟨hp', hm⟩
  refine ⟨hp', ?_, ?_, Line.of_inv Devm.getStor (by
    unfold mstoreAt
    line_inv) run⟩
  · rw [hm]
    exact hwf.write _ _
  · rw [hm]
    exact Mem.Reads.write hwf hr _ _

private theorem prefix_of_tagTop
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {region : Nat} {value : B256}
    (hp : value :: xs <<+ pre.stack)
    (run : Line.Run sevm pre (tagTop region) post) :
    slot region value :: xs <<+ post.stack ∧
      pre.memory = post.memory ∧
      Devm.getStor pre = Devm.getStor post := by
  unfold tagTop at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 := prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run with ⟨s2, q2, hnil⟩
  cases hnil
  refine ⟨?_, Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2 Line.Run.nil)),
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2 Line.Run.nil))⟩
  · change (regionWord region ||| value) :: xs <<+ post.stack
    exact prefix_of_or q2 hp1

private theorem prefix_of_targetKey_image
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {img : Bytes} {target : B256}
    (hp : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hread : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (run : Line.Run sevm pre targetKey post) :
    assignmentSlot target :: xs <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory img ∧
      Devm.getStor pre = Devm.getStor post := by
  unfold targetKey at run
  rcases of_run_append (loadWord targetWord) run with
    ⟨mid, hload, htag⟩
  rcases prefix_of_loadWord_image hp hwf hr hread hload with
    ⟨hp1, hwf1, hr1, hs1⟩
  rcases prefix_of_tagTop hp1 htag with ⟨hp2, hm2, hs2⟩
  refine ⟨?_, ?_, ?_, hs1.trans hs2⟩
  · simpa [assignmentSlot] using hp2
  · rw [← hm2]
    exact hwf1
  · rw [← hm2]
    exact hr1

private theorem prefix_of_previousCountKey_image
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {img : Bytes} {oldPauser : B256}
    (hp : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hread : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (run : Line.Run sevm pre previousCountKey post) :
    countSlot oldPauser :: xs <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory img ∧
      Devm.getStor pre = Devm.getStor post := by
  unfold previousCountKey at run
  rcases of_run_append (loadWord previousPauserWord) run with
    ⟨mid, hload, htag⟩
  rcases prefix_of_loadWord_image hp hwf hr hread hload with
    ⟨hp1, hwf1, hr1, hs1⟩
  rcases prefix_of_tagTop hp1 htag with ⟨hp2, hm2, hs2⟩
  refine ⟨?_, ?_, ?_, hs1.trans hs2⟩
  · simpa [countSlot] using hp2
  · rw [← hm2]
    exact hwf1
  · rw [← hm2]
    exact hr1

private theorem prefix_of_newCountKey_image
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {img : Bytes} {newPauser : B256}
    (hp : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hread : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (run : Line.Run sevm pre newCountKey post) :
    countSlot newPauser :: xs <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory img ∧
      Devm.getStor pre = Devm.getStor post := by
  unfold newCountKey at run
  rcases of_run_append (loadWord newPauserWord) run with
    ⟨mid, hload, htag⟩
  rcases prefix_of_loadWord_image hp hwf hr hread hload with
    ⟨hp1, hwf1, hr1, hs1⟩
  rcases prefix_of_tagTop hp1 htag with ⟨hp2, hm2, hs2⟩
  refine ⟨?_, ?_, ?_, hs1.trans hs2⟩
  · simpa [countSlot] using hp2
  · rw [← hm2]
    exact hwf1
  · rw [← hm2]
    exact hr1

private theorem prefix_of_targetIndexKey_image
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {img : Bytes} {target : B256}
    (hp : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hread : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (run : Line.Run sevm pre targetIndexKey post) :
    indexSlot target :: xs <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory img ∧
      Devm.getStor pre = Devm.getStor post := by
  unfold targetIndexKey at run
  rcases of_run_append (loadWord targetWord) run with
    ⟨mid, hload, htag⟩
  rcases prefix_of_loadWord_image hp hwf hr hread hload with
    ⟨hp1, hwf1, hr1, hs1⟩
  rcases prefix_of_tagTop hp1 htag with ⟨hp2, hm2, hs2⟩
  refine ⟨?_, ?_, ?_, hs1.trans hs2⟩
  · simpa [indexSlot] using hp2
  · rw [← hm2]
    exact hwf1
  · rw [← hm2]
    exact hr1

private theorem prefix_of_taggedWordKey_image
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    {img : Bytes} {word value : B256} {region : Nat}
    (hp : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hread : Bytes.toB256
      (img.sliceD (word * 32).toNat 32 0) = value)
    (run : Line.Run sevm pre (loadWord word ++ tagTop region) post) :
    slot region value :: xs <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory img ∧
      Devm.getStor pre = Devm.getStor post := by
  rcases of_run_append (loadWord word) run with ⟨mid, hload, htag⟩
  rcases prefix_of_loadWord_image hp hwf hr hread hload with
    ⟨hp1, hwf1, hr1, hs1⟩
  rcases prefix_of_tagTop hp1 htag with ⟨hp2, hm2, hs2⟩
  refine ⟨hp2, ?_, ?_, hs1.trans hs2⟩
  · rw [← hm2]
    exact hwf1
  · rw [← hm2]
    exact hr1

private theorem pausableZeroError_not_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm} :
    ¬ Func.Run fs sevm pre pausableZeroError post := by
  intro h
  dsimp [pausableZeroError, Func.revertSelector] at h
  rcases of_run_next h with ⟨s1, _, h1⟩
  rcases of_run_next h1 with ⟨s2, _, h2⟩
  rcases of_run_next h2 with ⟨s3, _, h3⟩
  rcases of_run_next h3 with ⟨s4, _, h4⟩
  rcases of_run_next h4 with ⟨s5, _, h5⟩
  cases h5 with
  | last hrun =>
      simp only [Linst.Run, Linst.run] at hrun
      rcases Except.bind_eq_ok hrun with ⟨v1, h1, h2⟩
      rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
      rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
      contradiction

/-- `Devm.getCode` reads only the world, so a state-preserving step carries the
whole account-code map.  The two stack-only steps a `Func` walk crosses — the
branch pop and the tail-call burn — are exactly of that shape, and every
instruction the Registry kernel decodes leaves the map alone outright. -/
private theorem getCode_of_state_eq {a b : Devm} (h : a.state = b.state) :
    Devm.getCode a = Devm.getCode b := by
  funext x
  simp only [Devm.getCode, Devm.getAcct]
  rw [h]

/-- A successful source kernel run necessarily takes the nonzero-target arm;
the result also exposes that residual arm for the Registry-write inversion. -/
theorem setPauser_run_extracts_nonzero_guard
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {target : B256}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hread : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (herrorLookup : fs[pausableZeroErrorSlot]? = some pausableZeroError)
    (hrun : Func.Run fs sevm pre setPauserKernel final) :
    target ≠ 0 ∧
      ∃ guardPre,
        pre.stack <<+ guardPre.stack ∧
        Mem.Wf guardPre.memory ∧
        Mem.Reads guardPre.memory img ∧
        Devm.getStor pre = Devm.getStor guardPre ∧
        Devm.getCode pre = Devm.getCode guardPre ∧
        Func.Run fs sevm guardPre
          (targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
            loadWord newPauserWord +++ targetKey +++ sstore :::
            iszero :::
            ((.call appendTargetSlot) <?>
              (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
                previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
          final := by
  simp only [setPauserKernel] at hrun
  rcases of_run_prepend (loadWord targetWord ++ [iszero]) _ hrun with
    ⟨s3, hprefix, hbranch⟩
  rcases of_run_append (loadWord targetWord) hprefix with
    ⟨s2, hload, hiszeroLine⟩
  rcases prefix_of_loadWord_image
      (xs := pre.stack) (value := target)
      (by simpa only [List.append_nil] using pref_append pre.stack [])
      hwf hr hread hload with
    ⟨htargetPrefix, hwf2, hr2, hstorLoad⟩
  rcases Line.of_run_cons hiszeroLine with
    ⟨s3', hiszero, hnil⟩
  cases hnil
  have hflagPrefix : (target =? 0) :: pre.stack <<+ s3.stack :=
    prefix_of_iszero hiszero htargetPrefix
  have hmemIszero : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  have hr3 : Mem.Reads s3.memory img := by
    rw [← hmemIszero]
    exact hr2
  have hwf3 : Mem.Wf s3.memory := by
    rw [← hmemIszero]
    exact hwf2
  have hstorIszero : Devm.getStor s2 = Devm.getStor s3 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hiszero Line.Run.nil)
  cases hbranch with
  | zero hpop hbody =>
      rename_i guardPre
      have hflag := (popBurn_pref hpop hflagPrefix).1
      have hstack := (popBurn_pref hpop hflagPrefix).2
      have htarget : target ≠ 0 := by
        intro heq
        rw [heq] at hflag
        simp [B256.eqCheck] at hflag
        exact (by decide : (0 : B256) ≠ 1) hflag
      have hrGuard : Mem.Reads guardPre.memory img := by
        rw [← hpop.memory]
        exact hr3
      have hwfGuard : Mem.Wf guardPre.memory := by
        rw [← hpop.memory]
        exact hwf3
      have hstorPop : Devm.getStor s3 = Devm.getStor guardPre :=
        PopBurn.Inv.inv hpop
      exact ⟨htarget, _, hstack, hwfGuard, hrGuard,
        hstorLoad.trans (hstorIszero.trans hstorPop),
        (Line.of_inv Devm.getCode (by line_inv) hprefix).trans
          (getCode_of_state_eq hpop.state),
        hbody⟩
  | succ _ _ _ herror =>
      rcases of_run_call herror with ⟨body, errorPre, hget, _, hbody⟩
      rw [herrorLookup] at hget
      injection hget with heq
      subst body
      exact (pausableZeroError_not_run hbody).elim

/-- Invert the common nonzero-target prefix through its first Registry write.
The returned state is immediately after the assignment SSTORE; its residual
run still contains every count, array, index, and cleanup write. -/
theorem setPauser_run_extracts_assignment_write
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {entries : List Entry} {target newPauser : B256}
    {ca : Adr} {xs : Stack}
    (hstack : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htarget : nonzeroCanonicalAddress target)
    (_hnew : canonicalAddress newPauser)
    (hrun : Func.Run fs sevm pre
      (targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ sstore :::
        iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
      final) :
    ∃ oldPauser postAssign,
      oldPauser = assignmentAt entries target ∧
      oldPauser :: xs <<+ postAssign.stack ∧
      Mem.Wf postAssign.memory ∧
      Mem.Reads postAssign.memory
        (Bytes.writeAt img (previousPauserWord * 32).toNat
          oldPauser.toBytes) ∧
      Devm.getStor postAssign ca =
        (Devm.getStor pre ca).set (assignmentSlot target) newPauser ∧
      Devm.getCode pre = Devm.getCode postAssign ∧
      Func.Run fs sevm postAssign
        (iszero :::
          ((.call appendTargetSlot) <?>
            (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
              previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
        final := by
  rcases of_run_prepend targetKey _ hrun with ⟨sKey1, hkey1, h1⟩
  rcases of_run_next h1 with ⟨sLoad, hsload, h2⟩
  rcases of_run_next h2 with ⟨sDup, hdup, h3⟩
  rcases of_run_prepend (mstoreAt previousPauserWord) _ h3 with
    ⟨sPrev, hprev, h4⟩
  rcases of_run_prepend (loadWord newPauserWord) _ h4 with
    ⟨sNew, hnewLoad, h5⟩
  rcases of_run_prepend targetKey _ h5 with ⟨sKey2, hkey2, h6⟩
  rcases of_run_next h6 with ⟨postAssign, hstore, hresidual⟩
  rcases prefix_of_targetKey_image hstack hwf hr htargetRead hkey1 with
    ⟨hkeyPrefix, hwfKey, hrKey, hstorKey⟩
  rcases prefix_of_sload hsload hkeyPrefix with
    ⟨oldPauser, holdPrefix, holdRead⟩
  have hold : oldPauser = assignmentAt entries target := by
    calc
      oldPauser =
          (Devm.getStor sKey1 sevm.currentTarget).get
            (assignmentSlot target) := holdRead
      _ = (Devm.getStor pre ca).get (assignmentSlot target) := by
        rw [howner, ← congrFun hstorKey ca]
      _ = assignmentAt entries target := by
        simpa [logicalStorageOfStor] using hw.assignments target htarget.2
  have hdupPrefix :
      oldPauser :: oldPauser :: xs <<+ sDup.stack :=
    prefix_of_dup_val hdup (by show_nth) holdPrefix
  have hmemLoad : sKey1.memory = sLoad.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsload
  have hmemDup : sLoad.memory = sDup.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hdup
  have hwfDup : Mem.Wf sDup.memory := by
    rw [← hmemDup, ← hmemLoad]
    exact hwfKey
  have hrDup : Mem.Reads sDup.memory img := by
    rw [← hmemDup, ← hmemLoad]
    exact hrKey
  rcases of_run_mstoreAt_image hdupPrefix hwfDup hrDup hprev with
    ⟨hprevPrefix, hwfPrev, hrPrev, hstorPrev⟩
  let imgPrev :=
    Bytes.writeAt img (previousPauserWord * 32).toNat oldPauser.toBytes
  have hnewPrev : Bytes.toB256
      (imgPrev.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    have hoff :
        (newPauserWord * 32).toNat + 32 ≤
          (previousPauserWord * 32).toNat := by
      decide
    dsimp [imgPrev]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
    exact hnewRead
  rcases prefix_of_loadWord_image hprevPrefix hwfPrev hrPrev hnewPrev
      hnewLoad with ⟨hnewPrefix, hwfNew, hrNew, hstorNew⟩
  have htargetPrev : Bytes.toB256
      (imgPrev.sliceD (targetWord * 32).toNat 32 0) = target := by
    have hoff :
        (targetWord * 32).toNat + 32 ≤
          (previousPauserWord * 32).toNat := by
      decide
    dsimp [imgPrev]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
    exact htargetRead
  rcases prefix_of_targetKey_image hnewPrefix hwfNew hrNew htargetPrev hkey2 with
    ⟨hstorePrefix, hwfKey2, hrKey2, hstorKey2⟩
  have hmemStore : sKey2.memory = postAssign.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstore
  have hwfPost : Mem.Wf postAssign.memory := by
    rw [← hmemStore]
    exact hwfKey2
  have hrPost : Mem.Reads postAssign.memory imgPrev := by
    rw [← hmemStore]
    exact hrKey2
  have hstackPost : oldPauser :: xs <<+ postAssign.stack :=
    prefix_of_sstore hstore hstorePrefix
  have hstorLoad : Devm.getStor sKey1 = Devm.getStor sLoad :=
    Ninst.Hinv.inv (f := Devm.getStor) hsload
  have hstorDup : Devm.getStor sLoad = Devm.getStor sDup :=
    Ninst.Hinv.inv (f := Devm.getStor) hdup
  have hstorBefore : Devm.getStor pre = Devm.getStor sKey2 :=
    hstorKey.trans (hstorLoad.trans
      (hstorDup.trans (hstorPrev.trans (hstorNew.trans hstorKey2))))
  have hstorPost :
      Devm.getStor postAssign ca =
        (Devm.getStor pre ca).set (assignmentSlot target) newPauser := by
    have hs := sstore_getStor_set hstore hstorePrefix
    rw [howner] at hs
    exact hs.trans
      (congrArg
        (fun stor => stor.set (assignmentSlot target) newPauser)
        (congrFun hstorBefore ca).symm)
  have hcodePost : Devm.getCode pre = Devm.getCode postAssign := by
    rw [Line.of_inv Devm.getCode (by line_inv) hkey1,
      Ninst.Hinv.inv (f := Devm.getCode) hsload,
      Ninst.Hinv.inv (f := Devm.getCode) hdup,
      Line.of_inv Devm.getCode (by line_inv) hprev,
      Line.of_inv Devm.getCode (by line_inv) hnewLoad,
      Line.of_inv Devm.getCode (by line_inv) hkey2,
      Ninst.Hinv.inv (f := Devm.getCode) hstore]
  exact ⟨oldPauser, postAssign, hold, hstackPost, hwfPost, hrPost,
    hstorPost, hcodePost, hresidual⟩

private theorem setPauser_run_split_old_assignment
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {oldPauser : B256} {xs : Stack}
    (hstack : oldPauser :: xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hrun : Func.Run fs sevm pre
      (iszero :::
        ((.call appendTargetSlot) <?>
          (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
      final) :
    (oldPauser = 0 ∧
      ∃ appendPre,
        xs <<+ appendPre.stack ∧
        Mem.Wf appendPre.memory ∧
        Mem.Reads appendPre.memory img ∧
        Devm.getStor pre = Devm.getStor appendPre ∧
        Devm.getCode pre = Devm.getCode appendPre ∧
        Func.Run fs sevm appendPre (.call appendTargetSlot) final) ∨
    (oldPauser ≠ 0 ∧
      ∃ oldCountPre,
        xs <<+ oldCountPre.stack ∧
        Mem.Wf oldCountPre.memory ∧
        Mem.Reads oldCountPre.memory img ∧
        Devm.getStor pre = Devm.getStor oldCountPre ∧
        Devm.getCode pre = Devm.getCode oldCountPre ∧
        Func.Run fs sevm oldCountPre
          (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ sstore ::: .call afterOldPauserSlot)
          final) := by
  rcases of_run_next hrun with ⟨s1, hiszero, hbranch⟩
  have hflagPrefix : (oldPauser =? 0) :: xs <<+ s1.stack :=
    prefix_of_iszero hiszero hstack
  have hmemIszero : pre.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hiszero
  have hstorIszero : Devm.getStor pre = Devm.getStor s1 :=
    Ninst.Hinv.inv (f := Devm.getStor) hiszero
  cases hbranch with
  | zero hpop hbody =>
      rename_i oldCountPre
      have hflag := (popBurn_pref hpop hflagPrefix).1
      have htail := (popBurn_pref hpop hflagPrefix).2
      have hold : oldPauser ≠ 0 := by
        intro heq
        rw [heq] at hflag
        simp [B256.eqCheck] at hflag
        exact (by decide : (0 : B256) ≠ 1) hflag
      have hmem : pre.memory = oldCountPre.memory :=
        hmemIszero.trans hpop.memory
      right
      exact ⟨hold, oldCountPre, htail,
        hmem ▸ hwf, hmem ▸ hr,
        hstorIszero.trans (PopBurn.Inv.inv hpop),
        (Ninst.Hinv.inv (f := Devm.getCode) hiszero).trans
          (getCode_of_state_eq hpop.state),
        hbody⟩
  | succ hnz hpop hburn hbody =>
      rename_i w afterPop appendPre
      have hflag : (oldPauser =? 0) = w :=
        (List.of_cons_pref_of_cons_pref hflagPrefix
          (pref_of_split hpop.stack)).left
      have hold : oldPauser = 0 := by
        by_contra hne
        rw [B256.eqCheck, if_neg hne] at hflag
        exact hnz hflag.symm
      have htail : xs <<+ afterPop.stack := by
        have hflagPrefix' : w :: xs <<+ s1.stack := by
          rwa [← hflag]
        exact (popBurn_pref hpop hflagPrefix').2
      have htail' : xs <<+ appendPre.stack := by
        rw [← hburn.stack]
        exact htail
      have hmem : pre.memory = appendPre.memory :=
        hmemIszero.trans (hpop.memory.trans hburn.memory)
      left
      exact ⟨hold, appendPre, htail',
        hmem ▸ hwf, hmem ▸ hr,
        hstorIszero.trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn)),
        (Ninst.Hinv.inv (f := Devm.getCode) hiszero).trans
          ((getCode_of_state_eq hpop.state).trans
            (getCode_of_state_eq hburn.state)),
        hbody⟩

private theorem setPauser_run_extracts_old_count_write
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {entries : List Entry}
    {target newPauser oldPauser : B256} {index : Nat}
    {ca : Adr} {xs : Stack} {entryStor : Stor}
    (hstack : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hprevRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = oldPauser)
    (howner : sevm.currentTarget = ca)
    (hw : RegistryWitness (logicalStorageOfStor entryStor) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hstor : Devm.getStor pre ca =
      entryStor.set (assignmentSlot target) newPauser)
    (hrun : Func.Run fs sevm pre
      (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
        previousCountKey +++ sstore ::: .call afterOldPauserSlot)
      final) :
    ∃ postOld,
      xs <<+ postOld.stack ∧
      Mem.Wf postOld.memory ∧
      Mem.Reads postOld.memory img ∧
      Devm.getStor postOld ca =
        (entryStor.set (assignmentSlot target) newPauser).set
          (countSlot oldPauser)
          (Nat.toB256 (assignmentCount entries oldPauser - 1)) ∧
      Devm.getCode pre = Devm.getCode postOld ∧
      Func.Run fs sevm postOld (.call afterOldPauserSlot) final := by
  rcases of_run_prepend previousCountKey _ hrun with
    ⟨sKey1, hkey1, h1⟩
  rcases of_run_next h1 with ⟨sLoad, hsload, h2⟩
  rcases of_run_next h2 with ⟨sPush, hpush, h3⟩
  rcases of_run_next h3 with ⟨sSwap, hswap, h4⟩
  rcases of_run_next h4 with ⟨sSub, hsub, h5⟩
  rcases of_run_prepend previousCountKey _ h5 with
    ⟨sKey2, hkey2, h6⟩
  rcases of_run_next h6 with ⟨postOld, hstore, hresidual⟩
  rcases prefix_of_previousCountKey_image
      hstack hwf hr hprevRead hkey1 with
    ⟨hkeyPrefix, hwfKey, hrKey, hstorKey⟩
  rcases prefix_of_sload hsload hkeyPrefix with
    ⟨countWord, hcountPrefix, hcountRead⟩
  have holdValid : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hfamilies := registryAddressFamilies_pairwise
    htarget.2 htarget.2 holdValid.2
  have hcount :
      countWord = Nat.toB256 (assignmentCount entries oldPauser) := by
    calc
      countWord =
          (Devm.getStor sKey1 sevm.currentTarget).get
            (countSlot oldPauser) := hcountRead
      _ = (Devm.getStor pre ca).get (countSlot oldPauser) := by
        rw [howner, ← congrFun hstorKey ca]
      _ = (entryStor.set (assignmentSlot target) newPauser).get
          (countSlot oldPauser) := by rw [hstor]
      _ = entryStor.get (countSlot oldPauser) := by
        rw [Stor.get_set_ne _ hfamilies.2.1]
      _ = Nat.toB256 (assignmentCount entries oldPauser) := by
        simpa [logicalStorageOfStor] using
          hw.counts oldPauser holdValid.2
  rw [hcount] at hcountPrefix
  have hpushPrefix :
      (1 : B256) :: Nat.toB256 (assignmentCount entries oldPauser) :: xs
        <<+ sPush.stack :=
    prefix_of_push (of_run_pushB256 hpush) hcountPrefix
  have hswapPrefix :
      Nat.toB256 (assignmentCount entries oldPauser) :: (1 : B256) :: xs
        <<+ sSwap.stack :=
    Stack.prefix_of_swap
      (show Stack.Swap (0 : Fin 16).val
        ((1 : B256) :: Nat.toB256 (assignmentCount entries oldPauser) :: xs)
        (Nat.toB256 (assignmentCount entries oldPauser) :: (1 : B256) :: xs)
        from Stack.swapCore_zero)
      (of_run_swap hswap) hpushPrefix
  have hsubPrefix :
      Nat.toB256 (assignmentCount entries oldPauser - 1) :: xs
        <<+ sSub.stack := by
    have hp := prefix_of_sub hsub hswapPrefix
    rw [hw.assignmentCountWord_pred_eq_sub_one hfind]
    exact hp
  have harithStor : Devm.getStor sKey1 = Devm.getStor sSub :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hsload
        (Line.Run.cons hpush
          (Line.Run.cons hswap (Line.Run.cons hsub Line.Run.nil))))
  have harithMem : sKey1.memory = sSub.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hsload
        (Line.Run.cons hpush
          (Line.Run.cons hswap (Line.Run.cons hsub Line.Run.nil))))
  have hwfSub : Mem.Wf sSub.memory := by
    rw [← harithMem]
    exact hwfKey
  have hrSub : Mem.Reads sSub.memory img := by
    rw [← harithMem]
    exact hrKey
  rcases prefix_of_previousCountKey_image
      hsubPrefix hwfSub hrSub hprevRead hkey2 with
    ⟨hstorePrefix, hwfKey2, hrKey2, hstorKey2⟩
  have hmemStore : sKey2.memory = postOld.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstore
  have hwfPost : Mem.Wf postOld.memory := by
    rw [← hmemStore]
    exact hwfKey2
  have hrPost : Mem.Reads postOld.memory img := by
    rw [← hmemStore]
    exact hrKey2
  have hstackPost : xs <<+ postOld.stack :=
    prefix_of_sstore hstore hstorePrefix
  have hstorBefore : Devm.getStor pre = Devm.getStor sKey2 :=
    hstorKey.trans (harithStor.trans hstorKey2)
  have hstorPost :
      Devm.getStor postOld ca =
        (entryStor.set (assignmentSlot target) newPauser).set
          (countSlot oldPauser)
          (Nat.toB256 (assignmentCount entries oldPauser - 1)) := by
    have hs := sstore_getStor_set hstore hstorePrefix
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set (countSlot oldPauser)
        (Nat.toB256 (assignmentCount entries oldPauser - 1)))
      ((congrFun hstorBefore ca).symm.trans hstor))
  have hcodePost : Devm.getCode pre = Devm.getCode postOld := by
    rw [Line.of_inv Devm.getCode (by line_inv) hkey1,
      Ninst.Hinv.inv (f := Devm.getCode) hsload,
      Ninst.Hinv.inv (f := Devm.getCode) hpush,
      Ninst.Hinv.inv (f := Devm.getCode) hswap,
      Ninst.Hinv.inv (f := Devm.getCode) hsub,
      Line.of_inv Devm.getCode (by line_inv) hkey2,
      Ninst.Hinv.inv (f := Devm.getCode) hstore]
  exact ⟨postOld, hstackPost, hwfPost, hrPost, hstorPost, hcodePost,
    hresidual⟩

private theorem appendTarget_run_extracts_writes
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {entryStor : Stor} {entries : List Entry}
    {target newPauser : B256} {ca : Adr} {xs : Stack}
    (hstack : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (howner : sevm.currentTarget = ca)
    (hw : RegistryWitness (logicalStorageOfStor entryStor) entries)
    (hpreStor : Devm.getStor pre ca =
      entryStor.set (assignmentSlot target) newPauser)
    (htarget : nonzeroCanonicalAddress target)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hrun : Func.Run fs sevm pre appendTarget final) :
    ∃ postAppend,
      Nat.toB256 (entries.length + 1) :: xs <<+ postAppend.stack ∧
      Mem.Wf postAppend.memory ∧
      Mem.Reads postAppend.memory
        (Bytes.writeAt img (arrayLengthWord * 32).toNat
          (Nat.toB256 (entries.length + 1)).toBytes) ∧
      Devm.getStor postAppend ca =
        (((entryStor.set (assignmentSlot target) newPauser).set
          (arrayEntrySlot (Nat.toB256 (entries.length + 1))) target).set
          (indexSlot target) (Nat.toB256 (entries.length + 1))).set
          arrayLengthSlot (Nat.toB256 (entries.length + 1)) ∧
      Devm.getCode pre = Devm.getCode postAppend ∧
      Func.Run fs sevm postAppend afterOldPauser final := by
  simp only [appendTarget] at hrun
  rcases of_run_next hrun with ⟨sLenKey, hpushLen, h1⟩
  rcases of_run_next h1 with ⟨sLenLoad, hsloadLen, h2⟩
  rcases of_run_next h2 with ⟨sOne, hpushOne, h3⟩
  rcases of_run_next h3 with ⟨sAdd, hadd, h4⟩
  rcases of_run_next h4 with ⟨sDup, hdup, h5⟩
  rcases of_run_prepend (mstoreAt arrayLengthWord) _ h5 with
    ⟨sMem, hmemStore, h6⟩
  rcases of_run_prepend (loadWord targetWord) _ h6 with
    ⟨sTarget, htargetLoad, h7⟩
  rcases of_run_prepend (loadWord arrayLengthWord) _ h7 with
    ⟨sLength1, hlengthLoad1, h8⟩
  rcases of_run_prepend (tagTop arrayRegion) _ h8 with
    ⟨sArrayKey, harrayKey, h9⟩
  rcases of_run_next h9 with ⟨sStore1, hstore1, h10⟩
  rcases of_run_prepend (loadWord arrayLengthWord) _ h10 with
    ⟨sLength2, hlengthLoad2, h11⟩
  rcases of_run_prepend targetIndexKey _ h11 with
    ⟨sIndexKey, hindexKey, h12⟩
  rcases of_run_next h12 with ⟨sStore2, hstore2, h13⟩
  rcases of_run_prepend (loadWord arrayLengthWord) _ h13 with
    ⟨sLength3, hlengthLoad3, h14⟩
  rcases of_run_next h14 with ⟨sLengthKey, hpushLengthKey, h15⟩
  rcases of_run_next h15 with ⟨sStore3, hstore3, hcall⟩
  rcases of_run_call hcall with
    ⟨body, postAppend, hget, hburn, hbody⟩
  rw [hafterLookup] at hget
  injection hget with hbodyEq
  subst body
  have hpLenKey : arrayLengthSlot :: xs <<+ sLenKey.stack :=
    prefix_of_push (of_run_pushB256 hpushLen) hstack
  rcases prefix_of_sload hsloadLen hpLenKey with
    ⟨lengthWord, hpLength, hlengthRead⟩
  have hstorPush : Devm.getStor pre = Devm.getStor sLenKey :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushLen
  have hassignmentLength : assignmentSlot target ≠ arrayLengthSlot :=
    (registryAddressFamilies_ne_arrayLengthSlot
      htarget.2 htarget.2).1
  have hlengthWord : lengthWord = Nat.toB256 entries.length := by
    calc
      lengthWord =
          (Devm.getStor sLenKey sevm.currentTarget).get arrayLengthSlot :=
        hlengthRead
      _ = (Devm.getStor pre ca).get arrayLengthSlot := by
        rw [howner, ← congrFun hstorPush ca]
      _ = (entryStor.set (assignmentSlot target) newPauser).get
          arrayLengthSlot := by rw [hpreStor]
      _ = entryStor.get arrayLengthSlot :=
        Stor.get_set_ne entryStor hassignmentLength newPauser
      _ = Nat.toB256 entries.length := by
        simpa [logicalStorageOfStor] using hw.lengthWord
  have hpOne : (1 : B256) :: lengthWord :: xs <<+ sOne.stack :=
    prefix_of_push (of_run_pushB256 hpushOne) hpLength
  have hpNext : Nat.toB256 (entries.length + 1) :: xs <<+ sAdd.stack := by
    have hp := prefix_of_add hadd hpOne
    rw [hlengthWord] at hp
    rw [show (1 : B256) + Nat.toB256 entries.length =
      Nat.toB256 entries.length + 1 from B256.add_comm] at hp
    rw [← hw.freshLengthWord_eq_add_one] at hp
    exact hp
  have hpDup :
      Nat.toB256 (entries.length + 1) ::
        Nat.toB256 (entries.length + 1) :: xs <<+ sDup.stack :=
    prefix_of_dup_val hdup (by show_nth) hpNext
  have hmemLenLoad : sLenKey.memory = sLenLoad.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsloadLen
  have hmemOne : sLenLoad.memory = sOne.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpushOne
  have hmemAdd : sOne.memory = sAdd.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hadd
  have hmemDup : sAdd.memory = sDup.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hdup
  have hwfDup : Mem.Wf sDup.memory := by
    rw [← hmemDup, ← hmemAdd, ← hmemOne, ← hmemLenLoad,
      ← (Ninst.Hinv.inv (f := Devm.memory) hpushLen)]
    exact hwf
  have hrDup : Mem.Reads sDup.memory img := by
    rw [← hmemDup, ← hmemAdd, ← hmemOne, ← hmemLenLoad,
      ← (Ninst.Hinv.inv (f := Devm.memory) hpushLen)]
    exact hr
  rcases of_run_mstoreAt_image hpDup hwfDup hrDup hmemStore with
    ⟨hpMem, hwfMem, hrMem, hstorMem⟩
  let imgNext :=
    Bytes.writeAt img (arrayLengthWord * 32).toNat
      (Nat.toB256 (entries.length + 1)).toBytes
  have htargetNext : Bytes.toB256
      (imgNext.sliceD (targetWord * 32).toNat 32 0) = target := by
    have hoff :
        (targetWord * 32).toNat + 32 ≤
          (arrayLengthWord * 32).toNat := by decide
    dsimp [imgNext]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
    exact htargetRead
  have hlengthNext : Bytes.toB256
      (imgNext.sliceD (arrayLengthWord * 32).toNat 32 0) =
        Nat.toB256 (entries.length + 1) := by
    dsimp [imgNext]
    rw [show 32 = (Nat.toB256 (entries.length + 1)).toBytes.length by
      rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  rcases prefix_of_loadWord_image hpMem hwfMem hrMem htargetNext
      htargetLoad with
    ⟨hpTarget, hwfTarget, hrTarget, hstorTarget⟩
  rcases prefix_of_loadWord_image hpTarget hwfTarget hrTarget hlengthNext
      hlengthLoad1 with
    ⟨hpLength1, hwfLength1, hrLength1, hstorLength1⟩
  rcases prefix_of_tagTop hpLength1 harrayKey with
    ⟨hpArray0, hmemArray, hstorArray⟩
  have hpArray :
      arrayEntrySlot (Nat.toB256 (entries.length + 1)) ::
        target :: Nat.toB256 (entries.length + 1) :: xs <<+
          sArrayKey.stack := by
    simpa [arrayEntrySlot] using hpArray0
  have hwfArray : Mem.Wf sArrayKey.memory := by
    rw [← hmemArray]
    exact hwfLength1
  have hrArray : Mem.Reads sArrayKey.memory imgNext := by
    rw [← hmemArray]
    exact hrLength1
  have hpStore1 : Nat.toB256 (entries.length + 1) :: xs <<+
      sStore1.stack :=
    prefix_of_sstore hstore1 hpArray
  have hmemStore1 : sArrayKey.memory = sStore1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstore1
  have hwfStore1 : Mem.Wf sStore1.memory := by
    rw [← hmemStore1]
    exact hwfArray
  have hrStore1 : Mem.Reads sStore1.memory imgNext := by
    rw [← hmemStore1]
    exact hrArray
  have hstorLenLoad : Devm.getStor sLenKey = Devm.getStor sLenLoad :=
    Ninst.Hinv.inv (f := Devm.getStor) hsloadLen
  have hstorOne : Devm.getStor sLenLoad = Devm.getStor sOne :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushOne
  have hstorAdd : Devm.getStor sOne = Devm.getStor sAdd :=
    Ninst.Hinv.inv (f := Devm.getStor) hadd
  have hstorDup : Devm.getStor sAdd = Devm.getStor sDup :=
    Ninst.Hinv.inv (f := Devm.getStor) hdup
  have hstorBefore1 : Devm.getStor pre = Devm.getStor sArrayKey :=
    hstorPush.trans (hstorLenLoad.trans
      (hstorOne.trans (hstorAdd.trans
        (hstorDup.trans (hstorMem.trans
          (hstorTarget.trans (hstorLength1.trans hstorArray)))))))
  have hstor1 : Devm.getStor sStore1 ca =
      (entryStor.set (assignmentSlot target) newPauser).set
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) target := by
    have hs := sstore_getStor_set hstore1 hpArray
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) target)
      ((congrFun hstorBefore1 ca).symm.trans hpreStor))
  rcases prefix_of_loadWord_image hpStore1 hwfStore1 hrStore1 hlengthNext
      hlengthLoad2 with
    ⟨hpLength2, hwfLength2, hrLength2, hstorLength2⟩
  rcases prefix_of_targetIndexKey_image hpLength2 hwfLength2 hrLength2
      htargetNext hindexKey with
    ⟨hpIndex, hwfIndex, hrIndex, hstorIndex⟩
  have hpStore2 : Nat.toB256 (entries.length + 1) :: xs <<+
      sStore2.stack :=
    prefix_of_sstore hstore2 hpIndex
  have hmemStore2 : sIndexKey.memory = sStore2.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstore2
  have hwfStore2 : Mem.Wf sStore2.memory := by
    rw [← hmemStore2]
    exact hwfIndex
  have hrStore2 : Mem.Reads sStore2.memory imgNext := by
    rw [← hmemStore2]
    exact hrIndex
  have hstor2 : Devm.getStor sStore2 ca =
      ((entryStor.set (assignmentSlot target) newPauser).set
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) target).set
        (indexSlot target) (Nat.toB256 (entries.length + 1)) := by
    have hs := sstore_getStor_set hstore2 hpIndex
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set (indexSlot target)
        (Nat.toB256 (entries.length + 1)))
      ((congrFun (hstorLength2.trans hstorIndex) ca).symm.trans hstor1))
  rcases prefix_of_loadWord_image hpStore2 hwfStore2 hrStore2 hlengthNext
      hlengthLoad3 with
    ⟨hpLength3, hwfLength3, hrLength3, hstorLength3⟩
  have hpLengthKey :
      arrayLengthSlot :: Nat.toB256 (entries.length + 1) ::
        Nat.toB256 (entries.length + 1) :: xs <<+ sLengthKey.stack :=
    prefix_of_push (of_run_pushB256 hpushLengthKey) hpLength3
  have hpStore3 : Nat.toB256 (entries.length + 1) :: xs <<+
      sStore3.stack :=
    prefix_of_sstore hstore3 hpLengthKey
  have hmemLengthKey : sLength3.memory = sLengthKey.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpushLengthKey
  have hmemStore3 : sLengthKey.memory = sStore3.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstore3
  have hwfStore3 : Mem.Wf sStore3.memory := by
    rw [← hmemStore3, ← hmemLengthKey]
    exact hwfLength3
  have hrStore3 : Mem.Reads sStore3.memory imgNext := by
    rw [← hmemStore3, ← hmemLengthKey]
    exact hrLength3
  have hstorLengthKey : Devm.getStor sLength3 = Devm.getStor sLengthKey :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushLengthKey
  have hstor3 : Devm.getStor sStore3 ca =
      (((entryStor.set (assignmentSlot target) newPauser).set
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) target).set
        (indexSlot target) (Nat.toB256 (entries.length + 1))).set
        arrayLengthSlot (Nat.toB256 (entries.length + 1)) := by
    have hs := sstore_getStor_set hstore3 hpLengthKey
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set arrayLengthSlot
        (Nat.toB256 (entries.length + 1)))
      ((congrFun (hstorLength3.trans hstorLengthKey) ca).symm.trans hstor2))
  have hpPost : Nat.toB256 (entries.length + 1) :: xs <<+
      postAppend.stack := by
    rw [← hburn.stack]
    exact hpStore3
  have hwfPost : Mem.Wf postAppend.memory := by
    rw [← hburn.memory]
    exact hwfStore3
  have hrPost : Mem.Reads postAppend.memory imgNext := by
    rw [← hburn.memory]
    exact hrStore3
  have hstorPost : Devm.getStor postAppend ca =
      (((entryStor.set (assignmentSlot target) newPauser).set
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) target).set
        (indexSlot target) (Nat.toB256 (entries.length + 1))).set
        arrayLengthSlot (Nat.toB256 (entries.length + 1)) := by
    exact (congrFun (Burn.Inv.inv hburn).symm ca).trans hstor3
  have hcodePost : Devm.getCode pre = Devm.getCode postAppend := by
    rw [Ninst.Hinv.inv (f := Devm.getCode) hpushLen,
      Ninst.Hinv.inv (f := Devm.getCode) hsloadLen,
      Ninst.Hinv.inv (f := Devm.getCode) hpushOne,
      Ninst.Hinv.inv (f := Devm.getCode) hadd,
      Ninst.Hinv.inv (f := Devm.getCode) hdup,
      Line.of_inv Devm.getCode (by line_inv) hmemStore,
      Line.of_inv Devm.getCode (by line_inv) htargetLoad,
      Line.of_inv Devm.getCode (by line_inv) hlengthLoad1,
      Line.of_inv Devm.getCode (by line_inv) harrayKey,
      Ninst.Hinv.inv (f := Devm.getCode) hstore1,
      Line.of_inv Devm.getCode (by line_inv) hlengthLoad2,
      Line.of_inv Devm.getCode (by line_inv) hindexKey,
      Ninst.Hinv.inv (f := Devm.getCode) hstore2,
      Line.of_inv Devm.getCode (by line_inv) hlengthLoad3,
      Ninst.Hinv.inv (f := Devm.getCode) hpushLengthKey,
      Ninst.Hinv.inv (f := Devm.getCode) hstore3,
      getCode_of_state_eq hburn.state]
  exact ⟨postAppend, hpPost, hwfPost, hrPost, hstorPost, hcodePost, hbody⟩

private theorem afterOldPauser_run_split_new_assignment
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {newPauser : B256} {xs : Stack}
    (hstack : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hrun : Func.Run fs sevm pre afterOldPauser final) :
    (newPauser = 0 ∧
      ∃ removePre,
        xs <<+ removePre.stack ∧
        Mem.Wf removePre.memory ∧
        Mem.Reads removePre.memory img ∧
        Devm.getStor pre = Devm.getStor removePre ∧
        Devm.getCode pre = Devm.getCode removePre ∧
        Func.Run fs sevm removePre (.call removeTargetSlot) final) ∨
    (newPauser ≠ 0 ∧
      ∃ newCountPre,
        xs <<+ newCountPre.stack ∧
        Mem.Wf newCountPre.memory ∧
        Mem.Reads newCountPre.memory img ∧
        Devm.getStor pre = Devm.getStor newCountPre ∧
        Devm.getCode pre = Devm.getCode newCountPre ∧
        Func.Run fs sevm newCountPre
          (newCountKey +++ sload ::: pushB256 1 ::: add :::
            newCountKey +++ sstore ::: .call finishSetPauserSlot)
          final) := by
  simp only [afterOldPauser] at hrun
  rcases of_run_prepend (loadWord newPauserWord) _ hrun with
    ⟨sLoad, hload, h1⟩
  rcases of_run_next h1 with ⟨sFlag, hiszero, hbranch⟩
  rcases prefix_of_loadWord_image hstack hwf hr hnewRead hload with
    ⟨hnewPrefix, hwfLoad, hrLoad, hstorLoad⟩
  have hflagPrefix : (newPauser =? 0) :: xs <<+ sFlag.stack :=
    prefix_of_iszero hiszero hnewPrefix
  have hmemIszero : sLoad.memory = sFlag.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hiszero
  have hstorIszero : Devm.getStor sLoad = Devm.getStor sFlag :=
    Ninst.Hinv.inv (f := Devm.getStor) hiszero
  cases hbranch with
  | zero hpop hbody =>
      rename_i newCountPre
      have hflag := (popBurn_pref hpop hflagPrefix).1
      have htail := (popBurn_pref hpop hflagPrefix).2
      have hnew : newPauser ≠ 0 := by
        intro heq
        rw [heq] at hflag
        simp [B256.eqCheck] at hflag
        exact (by decide : (0 : B256) ≠ 1) hflag
      have hmem : sLoad.memory = newCountPre.memory :=
        hmemIszero.trans hpop.memory
      right
      exact ⟨hnew, newCountPre, htail,
        hmem ▸ hwfLoad, hmem ▸ hrLoad,
        hstorLoad.trans
          (hstorIszero.trans (PopBurn.Inv.inv hpop)),
        (Line.of_inv Devm.getCode (by line_inv) hload).trans
          ((Ninst.Hinv.inv (f := Devm.getCode) hiszero).trans
            (getCode_of_state_eq hpop.state)),
        hbody⟩
  | succ hnz hpop hburn hbody =>
      rename_i w afterPop removePre
      have hflag : (newPauser =? 0) = w :=
        (List.of_cons_pref_of_cons_pref hflagPrefix
          (pref_of_split hpop.stack)).left
      have hnew : newPauser = 0 := by
        by_contra hne
        rw [B256.eqCheck, if_neg hne] at hflag
        exact hnz hflag.symm
      have htail : xs <<+ afterPop.stack := by
        have hflagPrefix' : w :: xs <<+ sFlag.stack := by
          rwa [← hflag]
        exact (popBurn_pref hpop hflagPrefix').2
      have htail' : xs <<+ removePre.stack := by
        rw [← hburn.stack]
        exact htail
      have hmem : sLoad.memory = removePre.memory :=
        hmemIszero.trans (hpop.memory.trans hburn.memory)
      left
      exact ⟨hnew, removePre, htail',
        hmem ▸ hwfLoad, hmem ▸ hrLoad,
        hstorLoad.trans
          (hstorIszero.trans
            ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn))),
        (Line.of_inv Devm.getCode (by line_inv) hload).trans
          ((Ninst.Hinv.inv (f := Devm.getCode) hiszero).trans
            ((getCode_of_state_eq hpop.state).trans
              (getCode_of_state_eq hburn.state))),
        hbody⟩

private theorem afterOldPauser_run_extracts_new_count_write
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {newPauser : B256} {countBefore : Nat}
    {ca : Adr} {xs : Stack} {currentStor : Stor}
    (hstack : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hpreStor : Devm.getStor pre ca = currentStor)
    (hcountRead : currentStor.get (countSlot newPauser) =
      Nat.toB256 countBefore)
    (hsucc : Nat.toB256 (countBefore + 1) =
      Nat.toB256 countBefore + 1)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hrun : Func.Run fs sevm pre
      (newCountKey +++ sload ::: pushB256 1 ::: add :::
        newCountKey +++ sstore ::: .call finishSetPauserSlot)
      final) :
    ∃ postRegistry,
      xs <<+ postRegistry.stack ∧
      Mem.Wf postRegistry.memory ∧
      Mem.Reads postRegistry.memory img ∧
      Devm.getStor postRegistry ca =
        currentStor.set (countSlot newPauser)
          (Nat.toB256 (countBefore + 1)) ∧
      Devm.getCode pre = Devm.getCode postRegistry ∧
      Func.Run fs sevm postRegistry finishSetPauser final := by
  rcases of_run_prepend newCountKey _ hrun with
    ⟨sKey1, hkey1, h1⟩
  rcases of_run_next h1 with ⟨sLoad, hsload, h2⟩
  rcases of_run_next h2 with ⟨sPush, hpush, h3⟩
  rcases of_run_next h3 with ⟨sAdd, hadd, h4⟩
  rcases of_run_prepend newCountKey _ h4 with
    ⟨sKey2, hkey2, h5⟩
  rcases of_run_next h5 with ⟨sStore, hstore, hcall⟩
  rcases of_run_call hcall with
    ⟨body, postRegistry, hget, hburn, hbody⟩
  rw [hfinishLookup] at hget
  injection hget with hbodyEq
  subst body
  rcases prefix_of_newCountKey_image
      hstack hwf hr hnewRead hkey1 with
    ⟨hkeyPrefix, hwfKey, hrKey, hstorKey⟩
  rcases prefix_of_sload hsload hkeyPrefix with
    ⟨countWord, hcountPrefix, hcountActual⟩
  have hcount : countWord = Nat.toB256 countBefore := by
    calc
      countWord =
          (Devm.getStor sKey1 sevm.currentTarget).get
            (countSlot newPauser) := hcountActual
      _ = (Devm.getStor pre ca).get (countSlot newPauser) := by
        rw [howner, ← congrFun hstorKey ca]
      _ = currentStor.get (countSlot newPauser) := by rw [hpreStor]
      _ = Nat.toB256 countBefore := hcountRead
  rw [hcount] at hcountPrefix
  have hpushPrefix :
      (1 : B256) :: Nat.toB256 countBefore :: xs <<+ sPush.stack :=
    prefix_of_push (of_run_pushB256 hpush) hcountPrefix
  have haddPrefix :
      Nat.toB256 (countBefore + 1) :: xs <<+ sAdd.stack := by
    have hp := prefix_of_add hadd hpushPrefix
    rw [show (1 : B256) + Nat.toB256 countBefore =
      Nat.toB256 countBefore + 1 from B256.add_comm] at hp
    rw [← hsucc] at hp
    exact hp
  have harithMem : sKey1.memory = sAdd.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hsload
        (Line.Run.cons hpush (Line.Run.cons hadd Line.Run.nil)))
  have harithStor : Devm.getStor sKey1 = Devm.getStor sAdd :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hsload
        (Line.Run.cons hpush (Line.Run.cons hadd Line.Run.nil)))
  have hwfAdd : Mem.Wf sAdd.memory := by
    rw [← harithMem]
    exact hwfKey
  have hrAdd : Mem.Reads sAdd.memory img := by
    rw [← harithMem]
    exact hrKey
  rcases prefix_of_newCountKey_image
      haddPrefix hwfAdd hrAdd hnewRead hkey2 with
    ⟨hstorePrefix, hwfKey2, hrKey2, hstorKey2⟩
  have hmemStore : sKey2.memory = sStore.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstore
  have hwfStore : Mem.Wf sStore.memory := by
    rw [← hmemStore]
    exact hwfKey2
  have hrStore : Mem.Reads sStore.memory img := by
    rw [← hmemStore]
    exact hrKey2
  have hstackStore : xs <<+ sStore.stack :=
    prefix_of_sstore hstore hstorePrefix
  have hstorBefore : Devm.getStor pre = Devm.getStor sKey2 :=
    hstorKey.trans (harithStor.trans hstorKey2)
  have hstorStore : Devm.getStor sStore ca =
      currentStor.set (countSlot newPauser)
        (Nat.toB256 (countBefore + 1)) := by
    have hs := sstore_getStor_set hstore hstorePrefix
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set (countSlot newPauser)
        (Nat.toB256 (countBefore + 1)))
      ((congrFun hstorBefore ca).symm.trans hpreStor))
  have hstackPost : xs <<+ postRegistry.stack := by
    rw [← hburn.stack]
    exact hstackStore
  have hwfPost : Mem.Wf postRegistry.memory := by
    rw [← hburn.memory]
    exact hwfStore
  have hrPost : Mem.Reads postRegistry.memory img := by
    rw [← hburn.memory]
    exact hrStore
  have hstorPost : Devm.getStor postRegistry ca =
      currentStor.set (countSlot newPauser)
        (Nat.toB256 (countBefore + 1)) :=
    (congrFun (Burn.Inv.inv hburn).symm ca).trans hstorStore
  have hcodePost : Devm.getCode pre = Devm.getCode postRegistry := by
    rw [Line.of_inv Devm.getCode (by line_inv) hkey1,
      Ninst.Hinv.inv (f := Devm.getCode) hsload,
      Ninst.Hinv.inv (f := Devm.getCode) hpush,
      Ninst.Hinv.inv (f := Devm.getCode) hadd,
      Line.of_inv Devm.getCode (by line_inv) hkey2,
      Ninst.Hinv.inv (f := Devm.getCode) hstore,
      getCode_of_state_eq hburn.state]
  exact ⟨postRegistry, hstackPost, hwfPost, hrPost, hstorPost, hcodePost,
    hbody⟩

private theorem removeTarget_run_extracts_writes
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {currentStor : Stor}
    {target indexWord lengthWord lastTarget newLengthWord : B256}
    {ca : Adr} {xs : Stack}
    (hstack : xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (howner : sevm.currentTarget = ca)
    (hcurrent : Devm.getStor pre ca = currentStor)
    (hindexRead : currentStor.get (indexSlot target) = indexWord)
    (hlengthRead : currentStor.get arrayLengthSlot = lengthWord)
    (hlastRead : currentStor.get (arrayEntrySlot lengthWord) = lastTarget)
    (harith : lengthWord - 1 = newLengthWord)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hrun : Func.Run fs sevm pre removeTarget final) :
    ∃ postRemove,
      xs <<+ postRemove.stack ∧
      Mem.Wf postRemove.memory ∧
      Mem.Reads postRemove.memory
        (Bytes.writeAt
          (Bytes.writeAt
            (Bytes.writeAt img (removedIndexWord * 32).toNat
              indexWord.toBytes)
            (arrayLengthWord * 32).toNat lengthWord.toBytes)
          (lastTargetWord * 32).toNat lastTarget.toBytes) ∧
      Devm.getStor postRemove ca =
        (((((currentStor.set (arrayEntrySlot indexWord) lastTarget).set
          (indexSlot lastTarget) indexWord).set
          (arrayEntrySlot lengthWord) 0).set
          arrayLengthSlot newLengthWord).set
          (indexSlot target) 0) ∧
      Devm.getCode pre = Devm.getCode postRemove ∧
      Func.Run fs sevm postRemove finishSetPauser final := by
  simp only [removeTarget] at hrun
  rcases of_run_prepend targetIndexKey _ hrun with
    ⟨sIndexKey1, hindexKey1, h1⟩
  rcases of_run_next h1 with ⟨sIndexLoad, hsloadIndex, h2⟩
  rcases of_run_prepend (mstoreAt removedIndexWord) _ h2 with
    ⟨sIndexMem, hstoreIndexMem, h3⟩
  rcases of_run_next h3 with ⟨sLengthSlot, hpushLengthSlot, h4⟩
  rcases of_run_next h4 with ⟨sLengthLoad, hsloadLength, h5⟩
  rcases of_run_prepend (mstoreAt arrayLengthWord) _ h5 with
    ⟨sLengthMem, hstoreLengthMem, h6⟩
  rcases of_run_prepend (loadWord arrayLengthWord) _ h6 with
    ⟨sLengthForLast, hloadLengthForLast, h7⟩
  rcases of_run_prepend (tagTop arrayRegion) _ h7 with
    ⟨sLastKey, hlastKey, h8⟩
  rcases of_run_next h8 with ⟨sLastLoad, hsloadLast, h9⟩
  rcases of_run_prepend (mstoreAt lastTargetWord) _ h9 with
    ⟨sLastMem, hstoreLastMem, h10⟩
  rcases of_run_prepend (loadWord lastTargetWord) _ h10 with
    ⟨sLastForHole, hloadLastForHole, h11⟩
  rcases of_run_prepend (loadWord removedIndexWord) _ h11 with
    ⟨sIndexForHole, hloadIndexForHole, h12⟩
  rcases of_run_prepend (tagTop arrayRegion) _ h12 with
    ⟨sHoleKey, hholeKey, h13⟩
  rcases of_run_next h13 with ⟨sHoleStore, hstoreHole, h14⟩
  rcases of_run_prepend (loadWord removedIndexWord) _ h14 with
    ⟨sIndexForMoved, hloadIndexForMoved, h15⟩
  rcases of_run_prepend lastTargetIndexKey _ h15 with
    ⟨sMovedKey, hmovedKey, h16⟩
  rcases of_run_next h16 with ⟨sMovedStore, hstoreMoved, h17⟩
  rcases of_run_next h17 with ⟨sZeroTail, hpushZeroTail, h18⟩
  rcases of_run_prepend (loadWord arrayLengthWord) _ h18 with
    ⟨sLengthForTail, hloadLengthForTail, h19⟩
  rcases of_run_prepend (tagTop arrayRegion) _ h19 with
    ⟨sTailKey, htailKey, h20⟩
  rcases of_run_next h20 with ⟨sTailStore, hstoreTail, h21⟩
  rcases of_run_prepend (loadWord arrayLengthWord) _ h21 with
    ⟨sLengthForSub, hloadLengthForSub, h22⟩
  rcases of_run_next h22 with ⟨sOne, hpushOne, h23⟩
  rcases of_run_next h23 with ⟨sSwap, hswap, h24⟩
  rcases of_run_next h24 with ⟨sSub, hsub, h25⟩
  rcases of_run_next h25 with ⟨sLengthKey, hpushLengthKey, h26⟩
  rcases of_run_next h26 with ⟨sLengthStore, hstoreLength, h27⟩
  rcases of_run_next h27 with ⟨sZeroIndex, hpushZeroIndex, h28⟩
  rcases of_run_prepend targetIndexKey _ h28 with
    ⟨sRemovedKey, hremovedKey, h29⟩
  rcases of_run_next h29 with ⟨sRemovedStore, hstoreRemoved, hcall⟩
  rcases of_run_call hcall with
    ⟨body, postRemove, hget, hburn, hbody⟩
  rw [hfinishLookup] at hget
  injection hget with hbodyEq
  subst body
  have hindexKeyFacts :=
    prefix_of_targetIndexKey_image hstack hwf hr htargetRead hindexKey1
  have hpIndexKey : indexSlot target :: xs <<+ sIndexKey1.stack :=
    hindexKeyFacts.1
  rcases prefix_of_sload hsloadIndex hpIndexKey with
    ⟨loadedIndex, hpLoadedIndex, hloadedIndexRead⟩
  have hstorIndexKey : Devm.getStor pre = Devm.getStor sIndexKey1 :=
    hindexKeyFacts.2.2.2
  have hloadedIndex : loadedIndex = indexWord := by
    calc
      loadedIndex = (Devm.getStor sIndexKey1 sevm.currentTarget).get
          (indexSlot target) := hloadedIndexRead
      _ = (Devm.getStor pre ca).get (indexSlot target) := by
        rw [howner, ← congrFun hstorIndexKey ca]
      _ = currentStor.get (indexSlot target) := by rw [hcurrent]
      _ = indexWord := hindexRead
  rw [hloadedIndex] at hpLoadedIndex
  have hmemIndexLoad : sIndexKey1.memory = sIndexLoad.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsloadIndex
  have hwfIndexLoad : Mem.Wf sIndexLoad.memory := by
    rw [← hmemIndexLoad]
    exact hindexKeyFacts.2.1
  have hrIndexLoad : Mem.Reads sIndexLoad.memory img := by
    rw [← hmemIndexLoad]
    exact hindexKeyFacts.2.2.1
  rcases of_run_mstoreAt_image hpLoadedIndex hwfIndexLoad hrIndexLoad
      hstoreIndexMem with
    ⟨hpIndexMem, hwfIndexMem, hrIndexMem, hstorIndexMem⟩
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat
    indexWord.toBytes
  have hpLengthSlot : arrayLengthSlot :: xs <<+ sLengthSlot.stack :=
    prefix_of_push (of_run_pushB256 hpushLengthSlot) hpIndexMem
  rcases prefix_of_sload hsloadLength hpLengthSlot with
    ⟨loadedLength, hpLoadedLength, hloadedLengthRead⟩
  have hstorIndexLoad : Devm.getStor sIndexKey1 = Devm.getStor sIndexLoad :=
    Ninst.Hinv.inv (f := Devm.getStor) hsloadIndex
  have hstorPushLength : Devm.getStor sIndexMem = Devm.getStor sLengthSlot :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushLengthSlot
  have hstorBeforeLength : Devm.getStor pre = Devm.getStor sLengthSlot :=
    hstorIndexKey.trans (hstorIndexLoad.trans
      (hstorIndexMem.trans hstorPushLength))
  have hloadedLength : loadedLength = lengthWord := by
    calc
      loadedLength = (Devm.getStor sLengthSlot sevm.currentTarget).get
          arrayLengthSlot := hloadedLengthRead
      _ = (Devm.getStor pre ca).get arrayLengthSlot := by
        rw [howner, ← congrFun hstorBeforeLength ca]
      _ = currentStor.get arrayLengthSlot := by rw [hcurrent]
      _ = lengthWord := hlengthRead
  rw [hloadedLength] at hpLoadedLength
  have hmemPushLength : sIndexMem.memory = sLengthSlot.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpushLengthSlot
  have hmemLengthLoad : sLengthSlot.memory = sLengthLoad.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsloadLength
  have hwfLengthLoad : Mem.Wf sLengthLoad.memory := by
    rw [← hmemLengthLoad, ← hmemPushLength]
    exact hwfIndexMem
  have hrLengthLoad : Mem.Reads sLengthLoad.memory imgIndex := by
    rw [← hmemLengthLoad, ← hmemPushLength]
    exact hrIndexMem
  rcases of_run_mstoreAt_image hpLoadedLength hwfLengthLoad hrLengthLoad
      hstoreLengthMem with
    ⟨hpLengthMem, hwfLengthMem, hrLengthMem, hstorLengthMem⟩
  let imgLength := Bytes.writeAt imgIndex (arrayLengthWord * 32).toNat
    lengthWord.toBytes
  have hlengthInLength : Bytes.toB256
      (imgLength.sliceD (arrayLengthWord * 32).toNat 32 0) = lengthWord := by
    dsimp [imgLength]
    rw [show 32 = lengthWord.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  rcases prefix_of_loadWord_image hpLengthMem hwfLengthMem hrLengthMem
      hlengthInLength hloadLengthForLast with
    ⟨hpLengthForLast, hwfLengthForLast, hrLengthForLast,
      hstorLengthForLast⟩
  rcases prefix_of_tagTop hpLengthForLast hlastKey with
    ⟨hpLastKey0, hmemLastKey, hstorLastKey⟩
  have hpLastKey : arrayEntrySlot lengthWord :: xs <<+ sLastKey.stack := by
    simpa [arrayEntrySlot] using hpLastKey0
  rcases prefix_of_sload hsloadLast hpLastKey with
    ⟨loadedLast, hpLoadedLast, hloadedLastRead⟩
  have hstorLengthLoad : Devm.getStor sLengthSlot = Devm.getStor sLengthLoad :=
    Ninst.Hinv.inv (f := Devm.getStor) hsloadLength
  have hstorBeforeLast : Devm.getStor pre = Devm.getStor sLastKey :=
    hstorBeforeLength.trans (hstorLengthLoad.trans
      (hstorLengthMem.trans (hstorLengthForLast.trans hstorLastKey)))
  have hloadedLast : loadedLast = lastTarget := by
    calc
      loadedLast = (Devm.getStor sLastKey sevm.currentTarget).get
          (arrayEntrySlot lengthWord) := hloadedLastRead
      _ = (Devm.getStor pre ca).get (arrayEntrySlot lengthWord) := by
        rw [howner, ← congrFun hstorBeforeLast ca]
      _ = currentStor.get (arrayEntrySlot lengthWord) := by rw [hcurrent]
      _ = lastTarget := hlastRead
  rw [hloadedLast] at hpLoadedLast
  have hmemLastLoad : sLastKey.memory = sLastLoad.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsloadLast
  have hwfLastLoad : Mem.Wf sLastLoad.memory := by
    rw [← hmemLastLoad, ← hmemLastKey]
    exact hwfLengthForLast
  have hrLastLoad : Mem.Reads sLastLoad.memory imgLength := by
    rw [← hmemLastLoad, ← hmemLastKey]
    exact hrLengthForLast
  rcases of_run_mstoreAt_image hpLoadedLast hwfLastLoad hrLastLoad
      hstoreLastMem with
    ⟨hpLastMem, hwfLastMem, hrLastMem, hstorLastMem⟩
  let imgLast := Bytes.writeAt imgLength (lastTargetWord * 32).toNat
    lastTarget.toBytes
  have htargetFinal : Bytes.toB256
      (imgLast.sliceD (targetWord * 32).toNat 32 0) = target := by
    have h1 : (targetWord * 32).toNat + 32 ≤
        (removedIndexWord * 32).toNat := by decide
    have h2 : (targetWord * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat := by decide
    have h3 : (targetWord * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat := by decide
    dsimp [imgLast, imgLength, imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ h3,
      Bytes.sliceD_writeAt_before _ _ _ _ _ h2,
      Bytes.sliceD_writeAt_before _ _ _ _ _ h1]
    exact htargetRead
  have hindexFinal : Bytes.toB256
      (imgLast.sliceD (removedIndexWord * 32).toNat 32 0) = indexWord := by
    have h2 : (removedIndexWord * 32).toNat + 32 ≤
        (arrayLengthWord * 32).toNat := by decide
    have h3 : (removedIndexWord * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat := by decide
    dsimp [imgLast, imgLength, imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ h3,
      Bytes.sliceD_writeAt_before _ _ _ _ _ h2]
    rw [show 32 = indexWord.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hlengthFinal : Bytes.toB256
      (imgLast.sliceD (arrayLengthWord * 32).toNat 32 0) = lengthWord := by
    have h3 : (arrayLengthWord * 32).toNat + 32 ≤
        (lastTargetWord * 32).toNat := by decide
    dsimp [imgLast, imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ h3]
    rw [show 32 = lengthWord.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hlastFinal : Bytes.toB256
      (imgLast.sliceD (lastTargetWord * 32).toNat 32 0) = lastTarget := by
    dsimp [imgLast]
    rw [show 32 = lastTarget.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  rcases prefix_of_loadWord_image hpLastMem hwfLastMem hrLastMem hlastFinal
      hloadLastForHole with
    ⟨hpLastForHole, hwfLastForHole, hrLastForHole, hstorLastForHole⟩
  rcases prefix_of_loadWord_image hpLastForHole hwfLastForHole hrLastForHole
      hindexFinal hloadIndexForHole with
    ⟨hpIndexForHole, hwfIndexForHole, hrIndexForHole,
      hstorIndexForHole⟩
  rcases prefix_of_tagTop hpIndexForHole hholeKey with
    ⟨hpHole0, hmemHole, hstorHoleKey⟩
  have hpHole : arrayEntrySlot indexWord :: lastTarget :: xs <<+
      sHoleKey.stack := by
    simpa [arrayEntrySlot] using hpHole0
  have hmemStoreHole : sHoleKey.memory = sHoleStore.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstoreHole
  have hpAfterHole : xs <<+ sHoleStore.stack :=
    prefix_of_sstore hstoreHole hpHole
  have hwfAfterHole : Mem.Wf sHoleStore.memory := by
    rw [← hmemStoreHole, ← hmemHole]
    exact hwfIndexForHole
  have hrAfterHole : Mem.Reads sHoleStore.memory imgLast := by
    rw [← hmemStoreHole, ← hmemHole]
    exact hrIndexForHole
  have hstorLastLoad : Devm.getStor sLastKey = Devm.getStor sLastLoad :=
    Ninst.Hinv.inv (f := Devm.getStor) hsloadLast
  have hstorBeforeHole : Devm.getStor pre = Devm.getStor sHoleKey :=
    hstorBeforeLast.trans (hstorLastLoad.trans
      (hstorLastMem.trans (hstorLastForHole.trans
        (hstorIndexForHole.trans hstorHoleKey))))
  have hstorHole : Devm.getStor sHoleStore ca =
      currentStor.set (arrayEntrySlot indexWord) lastTarget := by
    have hs := sstore_getStor_set hstoreHole hpHole
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set (arrayEntrySlot indexWord) lastTarget)
      ((congrFun hstorBeforeHole ca).symm.trans hcurrent))
  rcases prefix_of_loadWord_image hpAfterHole hwfAfterHole hrAfterHole
      hindexFinal hloadIndexForMoved with
    ⟨hpIndexForMoved, hwfIndexForMoved, hrIndexForMoved,
      hstorIndexForMoved⟩
  have hmovedKeyRun : Line.Run sevm sIndexForMoved
      (loadWord lastTargetWord ++ tagTop indexRegion) sMovedKey := by
    simpa [lastTargetIndexKey] using hmovedKey
  rcases prefix_of_taggedWordKey_image hpIndexForMoved hwfIndexForMoved
      hrIndexForMoved hlastFinal hmovedKeyRun with
    ⟨hpMoved0, hwfMoved, hrMoved, hstorMovedKey⟩
  have hpMoved : indexSlot lastTarget :: indexWord :: xs <<+
      sMovedKey.stack := by
    simpa [indexSlot] using hpMoved0
  have hpAfterMoved : xs <<+ sMovedStore.stack :=
    prefix_of_sstore hstoreMoved hpMoved
  have hmemMovedStore : sMovedKey.memory = sMovedStore.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstoreMoved
  have hwfAfterMoved : Mem.Wf sMovedStore.memory := by
    rw [← hmemMovedStore]
    exact hwfMoved
  have hrAfterMoved : Mem.Reads sMovedStore.memory imgLast := by
    rw [← hmemMovedStore]
    exact hrMoved
  have hstorMoved : Devm.getStor sMovedStore ca =
      (currentStor.set (arrayEntrySlot indexWord) lastTarget).set
        (indexSlot lastTarget) indexWord := by
    have hs := sstore_getStor_set hstoreMoved hpMoved
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set (indexSlot lastTarget) indexWord)
      ((congrFun (hstorIndexForMoved.trans hstorMovedKey) ca).symm.trans
        hstorHole))
  have hpZeroTail : (0 : B256) :: xs <<+ sZeroTail.stack :=
    prefix_of_push (of_run_pushB256 hpushZeroTail) hpAfterMoved
  have hmemPushZeroTail : sMovedStore.memory = sZeroTail.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpushZeroTail
  have hwfZeroTail : Mem.Wf sZeroTail.memory := by
    rw [← hmemPushZeroTail]
    exact hwfAfterMoved
  have hrZeroTail : Mem.Reads sZeroTail.memory imgLast := by
    rw [← hmemPushZeroTail]
    exact hrAfterMoved
  rcases prefix_of_loadWord_image hpZeroTail hwfZeroTail hrZeroTail
      hlengthFinal hloadLengthForTail with
    ⟨hpLengthForTail, hwfLengthForTail, hrLengthForTail,
      hstorLengthForTail⟩
  rcases prefix_of_tagTop hpLengthForTail htailKey with
    ⟨hpTail0, hmemTail, hstorTailKey⟩
  have hpTail : arrayEntrySlot lengthWord :: (0 : B256) :: xs <<+
      sTailKey.stack := by
    simpa [arrayEntrySlot] using hpTail0
  have hpAfterTail : xs <<+ sTailStore.stack :=
    prefix_of_sstore hstoreTail hpTail
  have hmemTailStore : sTailKey.memory = sTailStore.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstoreTail
  have hwfAfterTail : Mem.Wf sTailStore.memory := by
    rw [← hmemTailStore, ← hmemTail]
    exact hwfLengthForTail
  have hrAfterTail : Mem.Reads sTailStore.memory imgLast := by
    rw [← hmemTailStore, ← hmemTail]
    exact hrLengthForTail
  have hstorPushZeroTail : Devm.getStor sMovedStore = Devm.getStor sZeroTail :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushZeroTail
  have hstorTail : Devm.getStor sTailStore ca =
      ((currentStor.set (arrayEntrySlot indexWord) lastTarget).set
        (indexSlot lastTarget) indexWord).set
        (arrayEntrySlot lengthWord) 0 := by
    have hs := sstore_getStor_set hstoreTail hpTail
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set (arrayEntrySlot lengthWord) 0)
      ((congrFun (hstorPushZeroTail.trans
        (hstorLengthForTail.trans hstorTailKey)) ca).symm.trans hstorMoved))
  rcases prefix_of_loadWord_image hpAfterTail hwfAfterTail hrAfterTail
      hlengthFinal hloadLengthForSub with
    ⟨hpLengthForSub, hwfLengthForSub, hrLengthForSub,
      hstorLengthForSub⟩
  have hpOne : (1 : B256) :: lengthWord :: xs <<+ sOne.stack :=
    prefix_of_push (of_run_pushB256 hpushOne) hpLengthForSub
  have hpSwap : lengthWord :: (1 : B256) :: xs <<+ sSwap.stack :=
    Stack.prefix_of_swap
      (show Stack.Swap (0 : Fin 16).val
        ((1 : B256) :: lengthWord :: xs)
        (lengthWord :: (1 : B256) :: xs)
        from Stack.swapCore_zero)
      (of_run_swap hswap) hpOne
  have hpSub : newLengthWord :: xs <<+ sSub.stack := by
    have hp := prefix_of_sub hsub hpSwap
    rw [harith] at hp
    exact hp
  have hpLengthKey : arrayLengthSlot :: newLengthWord :: xs <<+
      sLengthKey.stack :=
    prefix_of_push (of_run_pushB256 hpushLengthKey) hpSub
  have hpAfterLength : xs <<+ sLengthStore.stack :=
    prefix_of_sstore hstoreLength hpLengthKey
  have hmemOne : sLengthForSub.memory = sOne.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpushOne
  have hmemSwap : sOne.memory = sSwap.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hswap
  have hmemSub : sSwap.memory = sSub.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hsub
  have hmemLengthKey : sSub.memory = sLengthKey.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpushLengthKey
  have hmemLengthStore : sLengthKey.memory = sLengthStore.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstoreLength
  have hwfAfterLength : Mem.Wf sLengthStore.memory := by
    rw [← hmemLengthStore, ← hmemLengthKey, ← hmemSub,
      ← hmemSwap, ← hmemOne]
    exact hwfLengthForSub
  have hrAfterLength : Mem.Reads sLengthStore.memory imgLast := by
    rw [← hmemLengthStore, ← hmemLengthKey, ← hmemSub,
      ← hmemSwap, ← hmemOne]
    exact hrLengthForSub
  have hstorOne : Devm.getStor sLengthForSub = Devm.getStor sOne :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushOne
  have hstorSwap : Devm.getStor sOne = Devm.getStor sSwap :=
    Ninst.Hinv.inv (f := Devm.getStor) hswap
  have hstorSub : Devm.getStor sSwap = Devm.getStor sSub :=
    Ninst.Hinv.inv (f := Devm.getStor) hsub
  have hstorLengthKey : Devm.getStor sSub = Devm.getStor sLengthKey :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushLengthKey
  have hstorLength : Devm.getStor sLengthStore ca =
      (((currentStor.set (arrayEntrySlot indexWord) lastTarget).set
        (indexSlot lastTarget) indexWord).set
        (arrayEntrySlot lengthWord) 0).set
        arrayLengthSlot newLengthWord := by
    have hs := sstore_getStor_set hstoreLength hpLengthKey
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set arrayLengthSlot newLengthWord)
      ((congrFun (hstorLengthForSub.trans
        (hstorOne.trans (hstorSwap.trans
          (hstorSub.trans hstorLengthKey)))) ca).symm.trans hstorTail))
  have hpZeroIndex : (0 : B256) :: xs <<+ sZeroIndex.stack :=
    prefix_of_push (of_run_pushB256 hpushZeroIndex) hpAfterLength
  have hmemPushZeroIndex : sLengthStore.memory = sZeroIndex.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpushZeroIndex
  have hwfZeroIndex : Mem.Wf sZeroIndex.memory := by
    rw [← hmemPushZeroIndex]
    exact hwfAfterLength
  have hrZeroIndex : Mem.Reads sZeroIndex.memory imgLast := by
    rw [← hmemPushZeroIndex]
    exact hrAfterLength
  have hremovedKeyRun : Line.Run sevm sZeroIndex
      (loadWord targetWord ++ tagTop indexRegion) sRemovedKey := by
    simpa [targetIndexKey] using hremovedKey
  rcases prefix_of_taggedWordKey_image hpZeroIndex hwfZeroIndex
      hrZeroIndex htargetFinal hremovedKeyRun with
    ⟨hpRemoved0, hwfRemoved, hrRemoved, hstorRemovedKey⟩
  have hpRemoved : indexSlot target :: (0 : B256) :: xs <<+
      sRemovedKey.stack := by
    simpa [indexSlot] using hpRemoved0
  have hpAfterRemoved : xs <<+ sRemovedStore.stack :=
    prefix_of_sstore hstoreRemoved hpRemoved
  have hmemRemovedStore : sRemovedKey.memory = sRemovedStore.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstoreRemoved
  have hwfAfterRemoved : Mem.Wf sRemovedStore.memory := by
    rw [← hmemRemovedStore]
    exact hwfRemoved
  have hrAfterRemoved : Mem.Reads sRemovedStore.memory imgLast := by
    rw [← hmemRemovedStore]
    exact hrRemoved
  have hstorPushZeroIndex :
      Devm.getStor sLengthStore = Devm.getStor sZeroIndex :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushZeroIndex
  have hstorRemoved : Devm.getStor sRemovedStore ca =
      (((((currentStor.set (arrayEntrySlot indexWord) lastTarget).set
        (indexSlot lastTarget) indexWord).set
        (arrayEntrySlot lengthWord) 0).set
        arrayLengthSlot newLengthWord).set
        (indexSlot target) 0) := by
    have hs := sstore_getStor_set hstoreRemoved hpRemoved
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set (indexSlot target) 0)
      ((congrFun (hstorPushZeroIndex.trans hstorRemovedKey) ca).symm.trans
        hstorLength))
  have hpPost : xs <<+ postRemove.stack := by
    rw [← hburn.stack]
    exact hpAfterRemoved
  have hwfPost : Mem.Wf postRemove.memory := by
    rw [← hburn.memory]
    exact hwfAfterRemoved
  have hrPost : Mem.Reads postRemove.memory imgLast := by
    rw [← hburn.memory]
    exact hrAfterRemoved
  have hstorPost : Devm.getStor postRemove ca =
      (((((currentStor.set (arrayEntrySlot indexWord) lastTarget).set
        (indexSlot lastTarget) indexWord).set
        (arrayEntrySlot lengthWord) 0).set
        arrayLengthSlot newLengthWord).set
        (indexSlot target) 0) :=
    (congrFun (Burn.Inv.inv hburn).symm ca).trans hstorRemoved
  have hcodePost : Devm.getCode pre = Devm.getCode postRemove := by
    rw [Line.of_inv Devm.getCode (by line_inv) hindexKey1,
      Ninst.Hinv.inv (f := Devm.getCode) hsloadIndex,
      Line.of_inv Devm.getCode (by line_inv) hstoreIndexMem,
      Ninst.Hinv.inv (f := Devm.getCode) hpushLengthSlot,
      Ninst.Hinv.inv (f := Devm.getCode) hsloadLength,
      Line.of_inv Devm.getCode (by line_inv) hstoreLengthMem,
      Line.of_inv Devm.getCode (by line_inv) hloadLengthForLast,
      Line.of_inv Devm.getCode (by line_inv) hlastKey,
      Ninst.Hinv.inv (f := Devm.getCode) hsloadLast,
      Line.of_inv Devm.getCode (by line_inv) hstoreLastMem,
      Line.of_inv Devm.getCode (by line_inv) hloadLastForHole,
      Line.of_inv Devm.getCode (by line_inv) hloadIndexForHole,
      Line.of_inv Devm.getCode (by line_inv) hholeKey,
      Ninst.Hinv.inv (f := Devm.getCode) hstoreHole,
      Line.of_inv Devm.getCode (by line_inv) hloadIndexForMoved,
      Line.of_inv Devm.getCode (by line_inv) hmovedKey,
      Ninst.Hinv.inv (f := Devm.getCode) hstoreMoved,
      Ninst.Hinv.inv (f := Devm.getCode) hpushZeroTail,
      Line.of_inv Devm.getCode (by line_inv) hloadLengthForTail,
      Line.of_inv Devm.getCode (by line_inv) htailKey,
      Ninst.Hinv.inv (f := Devm.getCode) hstoreTail,
      Line.of_inv Devm.getCode (by line_inv) hloadLengthForSub,
      Ninst.Hinv.inv (f := Devm.getCode) hpushOne,
      Ninst.Hinv.inv (f := Devm.getCode) hswap,
      Ninst.Hinv.inv (f := Devm.getCode) hsub,
      Ninst.Hinv.inv (f := Devm.getCode) hpushLengthKey,
      Ninst.Hinv.inv (f := Devm.getCode) hstoreLength,
      Ninst.Hinv.inv (f := Devm.getCode) hpushZeroIndex,
      Line.of_inv Devm.getCode (by line_inv) hremovedKey,
      Ninst.Hinv.inv (f := Devm.getCode) hstoreRemoved,
      getCode_of_state_eq hburn.state]
  exact ⟨postRemove, hpPost, hwfPost, hrPost, hstorPost, hcodePost, hbody⟩

private theorem appendedRegistryStorage_reads
    {s : Stor} {entries : List Entry} {target newPauser : B256}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hnew : canonicalAddress newPauser) :
    let next := Nat.toB256 (entries.length + 1)
    let current := (((s.set (assignmentSlot target) newPauser).set
      (arrayEntrySlot next) target).set (indexSlot target) next).set
      arrayLengthSlot next
    current.get (indexSlot target) = next ∧
    current.get arrayLengthSlot = next ∧
    current.get (arrayEntrySlot next) = target ∧
    current.get (countSlot newPauser) =
      Nat.toB256 (assignmentCount entries newPauser) ∧
    next - 1 = Nat.toB256 entries.length := by
  dsimp
  have hnext252 :
      (Nat.toB256 (entries.length + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hw.fresh_length_lt_2pow256]
    exact hw.fresh_length_lt_2pow252
  have hpair :=
    registryAddressFamilies_pairwise htarget.2 htarget.2 hnew
  have harray :=
    registryAddressFamilies_ne_arrayEntrySlot htarget.2 hnew hnext252
  have hlength :=
    registryAddressFamilies_ne_arrayLengthSlot htarget.2 hnew
  have hnext0 : Nat.toB256 (entries.length + 1) ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hw.fresh_length_lt_2pow256] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  have harrayLength :=
    arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnext0 hnext252
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Stor.get_set_ne _ (Ne.symm hlength.2.1), Stor.get_set_self]
  · rw [Stor.get_set_self]
  · rw [Stor.get_set_ne _ harrayLength,
      Stor.get_set_ne _ harray.2.1, Stor.get_set_self]
  · rw [Stor.get_set_ne _ (Ne.symm hlength.2.2),
      Stor.get_set_ne _ hpair.2.2,
      Stor.get_set_ne _ (Ne.symm harray.2.2),
      Stor.get_set_ne _ hpair.2.1]
    simpa [logicalStorageOfStor] using hw.counts newPauser hnew
  · symm
    simpa using natToB256_pred_eq_sub_one (entries.length + 1)
      (by omega) hw.fresh_length_lt_2pow256

private theorem reassignedRegistryStorage_newCount
    {s : Stor} {entries : List Entry}
    {target newPauser oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hnew : nonzeroCanonicalAddress newPauser)
    (hfind : findEntry entries target = some (index, oldPauser)) :
    let countBefore := assignmentCount entries newPauser -
      (if oldPauser = newPauser then 1 else 0)
    let current := (s.set (assignmentSlot target) newPauser).set
      (countSlot oldPauser)
      (Nat.toB256 (assignmentCount entries oldPauser - 1))
    current.get (countSlot newPauser) = Nat.toB256 countBefore ∧
    Nat.toB256 (countBefore + 1) = Nat.toB256 countBefore + 1 := by
  dsimp
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  have hpair :=
    registryAddressFamilies_pairwise htarget.2 htarget.2 hnew.2
  constructor
  · by_cases heq : oldPauser = newPauser
    · subst oldPauser
      rw [Stor.get_set_self]
      simp
    · have hcountNe : countSlot oldPauser ≠ countSlot newPauser := by
        intro hslots
        exact heq (countSlot_injective hold.2 hnew.2 hslots)
      rw [Stor.get_set_ne _ hcountNe, Stor.get_set_ne _ hpair.2.1]
      simp [heq]
      simpa [logicalStorageOfStor] using hw.counts newPauser hnew.2
  · apply natToB256_succ_eq_add_one
    have hcount := assignmentCount_le_length entries newPauser
    have hlength := hw.entries_length_le
    norm_num at hlength ⊢
    omega

private theorem foundRemovalStorage_reads
    {s : Stor} {entries : List Entry}
    {target oldPauser : B256} {index : Nat}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser)) :
    let current := (s.set (assignmentSlot target) 0).set
      (countSlot oldPauser)
      (Nat.toB256 (assignmentCount entries oldPauser - 1))
    current.get (indexSlot target) = Nat.toB256 (index + 1) ∧
    current.get arrayLengthSlot = Nat.toB256 entries.length ∧
    current.get (arrayEntrySlot (Nat.toB256 entries.length)) =
      sourceLastTarget entries ∧
    Nat.toB256 entries.length - 1 =
      Nat.toB256 (entries.length - 1) := by
  dsimp
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  obtain ⟨last, hlast⟩ := last_some_of_findEntry hfind
  have hlastMem := last_mem_of_last entries hlast
  have hlastValid := hw.targetsValid last hlastMem
  have hlength256 := hw.entries_length_lt_2pow256
  have hlength252 :
      (Nat.toB256 entries.length).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hlength256]
    exact hw.entries_length_lt_2pow252
  have htargetPair :=
    registryAddressFamilies_pairwise htarget.2 htarget.2 hold.2
  have hlengthFamilies :=
    registryAddressFamilies_ne_arrayLengthSlot htarget.2 hold.2
  have harrayFamilies :=
    registryAddressFamilies_ne_arrayEntrySlot
      htarget.2 hold.2 hlength252
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Stor.get_set_ne _ (Ne.symm htargetPair.2.2),
      Stor.get_set_ne _ htargetPair.1]
    simpa [logicalStorageOfStor, findEntry_oneBasedIndexAt hfind] using
      hw.indices target htarget.2
  · rw [Stor.get_set_ne _ hlengthFamilies.2.2,
      Stor.get_set_ne _ hlengthFamilies.1]
    simpa [logicalStorageOfStor] using hw.lengthWord
  · rw [Stor.get_set_ne _ harrayFamilies.2.2,
      Stor.get_set_ne _ harrayFamilies.1]
    have hindex : entries.length - 1 < entries.length := by
      have hi := findEntry_index_lt hfind
      omega
    have harray := hw.arrayWords (entries.length - 1) hindex
    rw [targetAt_last_of_last entries hlast] at harray
    change s.get (arrayEntrySlot (Nat.toB256 entries.length)) =
      sourceLastTarget entries
    rw [show sourceLastTarget entries = last.1 by
      simp [sourceLastTarget, hlast]]
    have hlengthPos : 1 ≤ entries.length := by
      have hi := findEntry_index_lt hfind
      omega
    simpa only [logicalStorageOfStor,
      Nat.sub_add_cancel hlengthPos] using harray
  · symm
    simpa using natToB256_pred_eq_sub_one entries.length
      (by
        have hi := findEntry_index_lt hfind
        omega)
      hlength256

/-- The found-target/zero-pauser path removes the entry by swap-pop and
replays the exact assignment clear, count decrement, moved-index repair,
tail clear, length decrement, and removed-index clear chronology. -/
theorem RegistryWitness.applyFoundZeroWrites
    {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    {target oldPauser : B256} {index : Nat}
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser)) :
    RegistryWitness
      (logicalStorageOfStor
        (applyRegistryWrites s
          [(assignmentSlot target, 0),
           (countSlot oldPauser,
             Nat.toB256 (assignmentCount entries oldPauser - 1)),
           (arrayEntrySlot (Nat.toB256 (index + 1)),
             sourceLastTarget entries),
           (indexSlot (sourceLastTarget entries), Nat.toB256 (index + 1)),
           (arrayEntrySlot (Nat.toB256 entries.length), 0),
           (arrayLengthSlot, Nat.toB256 (entries.length - 1)),
           (indexSlot target, 0)]))
      (swapPop entries index) := by
  have hindexLt := findEntry_index_lt hfind
  have hold : nonzeroCanonicalAddress oldPauser :=
    hw.pausersValid (target, oldPauser) (mem_of_findEntry hfind)
  obtain ⟨last, hlast⟩ := last_some_of_findEntry hfind
  have hlastMem := last_mem_of_last entries hlast
  have hlastTarget : nonzeroCanonicalAddress last.1 :=
    hw.targetsValid last hlastMem
  have hsource : sourceLastTarget entries = last.1 := by
    simp [sourceLastTarget, hlast]
  rw [hsource]
  have hindex256 : index + 1 < 2 ^ 256 := by
    have hbound := hw.entries_length_le
    norm_num at hbound ⊢
    omega
  have hindex252 : (Nat.toB256 (index + 1)).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hindex256]
    have hbound := hw.entries_length_le
    norm_num at hbound ⊢
    omega
  have hlength256 : entries.length < 2 ^ 256 :=
    hw.entries_length_lt_2pow256
  have hlength252 : (Nat.toB256 entries.length).toNat < 2 ^ 252 := by
    rw [B256.toNat_toB256_of_lt hlength256]
    exact hw.entries_length_lt_2pow252
  have hlengthWord0 : Nat.toB256 entries.length ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hlength256] at hnat
    simp only [B256.toNat_zero] at hnat
    omega
  have hlengthTail :=
    arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hlengthWord0 hlength252
  exact {
    targetsNodup := swapPop_targetsNodup_of_findEntry hfind hw.targetsNodup
    targetsValid := swapPop_targetsValid_of_findEntry hfind hw.targetsValid
    pausersValid := swapPop_pausersValid_of_findEntry hfind hw.pausersValid
    lengthWord := by
      have hfamilies :=
        registryAddressFamilies_ne_arrayLengthSlot htarget.2 hold.2
      have hlastFamilies :=
        registryAddressFamilies_ne_arrayLengthSlot hlastTarget.2 hold.2
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hfamilies.2.1, swapPop_length_of_findEntry hfind]
    arrayWords := by
      intro wantedIndex hwanted
      have hpostIndex : wantedIndex < entries.length - 1 := by
        rw [swapPop_length_of_findEntry hfind] at hwanted
        exact hwanted
      have hwantedOld : wantedIndex < entries.length := by omega
      have hwanted256 : wantedIndex + 1 < 2 ^ 256 := by
        have hbound := hw.entries_length_le
        norm_num at hbound ⊢
        omega
      have hwanted252 :
          (Nat.toB256 (wantedIndex + 1)).toNat < 2 ^ 252 := by
        rw [B256.toNat_toB256_of_lt hwanted256]
        have hbound := hw.entries_length_le
        norm_num at hbound ⊢
        omega
      have htargetArray :=
        registryAddressFamilies_ne_arrayEntrySlot
          htarget.2 hold.2 hwanted252
      have hlastArray :=
        registryAddressFamilies_ne_arrayEntrySlot
          hlastTarget.2 hold.2 hwanted252
      have hlengthArray := hw.arrayLengthSlot_ne_arrayEntrySlot hwantedOld
      have htail :
          arrayEntrySlot (Nat.toB256 entries.length) ≠
            arrayEntrySlot (Nat.toB256 (wantedIndex + 1)) := by
        intro heq
        have hnat := arrayEntrySlot_nat_injective_of_lt
          hw.entries_length_lt_2pow252
          (by
            have hbound := hw.entries_length_le
            norm_num at hbound ⊢
            omega) heq
        omega
      by_cases heq : wantedIndex = index
      · subst wantedIndex
        have htargetMoved :=
          targetAt_swapPop_moved_of_lt_last entries (index := index) (by omega)
        have htailHole :
            arrayEntrySlot (Nat.toB256 entries.length) ≠
              arrayEntrySlot (Nat.toB256 (index + 1)) := htail
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [htargetArray.2.1,
          hlastArray.2.1, htailHole, hlengthArray]
        rw [htargetMoved, targetAt_last_of_last entries hlast]
      · have hhole :
            arrayEntrySlot (Nat.toB256 (index + 1)) ≠
              arrayEntrySlot (Nat.toB256 (wantedIndex + 1)) := by
          intro hslots
          exact heq (hw.arrayEntrySlot_injective hindexLt hwantedOld hslots).symm
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [htargetArray.1, htargetArray.2.1, htargetArray.2.2,
          hlastArray.2.1, hhole, htail, hlengthArray]
        rw [targetAt_swapPop_of_ne entries hindexLt hpostIndex heq]
        simpa [logicalStorageOfStor] using hw.arrayWords wantedIndex hwantedOld
    assignments := by
      intro wanted hwanted
      have hhole :=
        registryAddressFamilies_ne_arrayEntrySlot hwanted hold.2 hindex252
      have htail :=
        registryAddressFamilies_ne_arrayEntrySlot hwanted hold.2 hlength252
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot hwanted hold.2
      have hcountPair :=
        registryAddressFamilies_pairwise hwanted htarget.2 hold.2
      have hlastPair :=
        registryAddressFamilies_pairwise hwanted hlastTarget.2 hold.2
      have htargetPair :=
        registryAddressFamilies_pairwise hwanted htarget.2 hold.2
      by_cases heq : wanted = target
      · subst wanted
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [Ne.symm hcountPair.2.1, Ne.symm hhole.1,
          Ne.symm hlastPair.1, Ne.symm htail.1, Ne.symm hlength.1,
          Ne.symm htargetPair.1,
          assignmentAt_swapPop_target_of_findEntry hfind hw.targetsNodup]
      · have hassignment : assignmentSlot target ≠ assignmentSlot wanted := by
          intro hslots
          exact (Ne.symm heq)
            (assignmentSlot_injective htarget.2 hwanted hslots)
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [hassignment, Ne.symm hcountPair.2.1, Ne.symm hhole.1,
          Ne.symm hlastPair.1, Ne.symm htail.1, Ne.symm hlength.1,
          Ne.symm htargetPair.1]
        rw [assignmentAt_swapPop_of_findEntry_ne hfind hw.targetsNodup heq]
        simpa [logicalStorageOfStor] using hw.assignments wanted hwanted
    indices := by
      intro wanted hwanted
      have hassignmentPair :=
        registryAddressFamilies_pairwise htarget.2 hwanted hold.2
      have hhole :=
        registryAddressFamilies_ne_arrayEntrySlot hwanted hold.2 hindex252
      have htail :=
        registryAddressFamilies_ne_arrayEntrySlot hwanted hold.2 hlength252
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot hwanted hold.2
      by_cases htargetEq : wanted = target
      · subst wanted
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [oneBasedIndexAt_swapPop_target_of_findEntry
          hfind hw.targetsNodup]
        rfl
      · have htargetIndex : indexSlot target ≠ indexSlot wanted := by
          intro hslots
          exact (Ne.symm htargetEq)
            (indexSlot_injective htarget.2 hwanted hslots)
        cases hwantedFind : findEntry entries wanted with
        | none =>
            have hneqLast : wanted ≠ last.1 := by
              intro heq
              apply findEntry_none_target_not_mem_targets hwantedFind
              rw [heq]
              exact List.mem_map.mpr ⟨last, hlastMem, rfl⟩
            have hlastIndex : indexSlot last.1 ≠ indexSlot wanted := by
              intro hslots
              exact (Ne.symm hneqLast)
                (indexSlot_injective hlastTarget.2 hwanted hslots)
            simp only [logicalStorageOfStor, applyRegistryWrites_get,
              List.foldl_cons, List.foldl_nil]
            simp [hassignmentPair.1, Ne.symm hassignmentPair.2.2,
              Ne.symm hhole.2.1, hlastIndex, Ne.symm htail.2.1,
              Ne.symm hlength.2.1, htargetIndex,
              oneBasedIndexAt_swapPop_of_findEntry_none hfind hwantedFind]
            have hbase := hw.indices wanted hwanted
            change s.get (indexSlot wanted) =
              Nat.toB256 (oneBasedIndexAt entries wanted) at hbase
            exact hbase.trans
              (congrArg Nat.toB256
                (findEntry_none_oneBasedIndexAt hwantedFind))
        | some found =>
            obtain ⟨wantedIndex, wantedPauser⟩ := found
            by_cases hlastEq : wanted = last.1
            · subst wanted
              have hnonself : index + 1 < entries.length := by
                by_contra hnot
                have hi : index = entries.length - 1 := by omega
                have htargetAt := findEntry_targetAt hfind
                rw [hi, targetAt_last_of_last entries hlast] at htargetAt
                exact htargetEq htargetAt
              simp only [logicalStorageOfStor, applyRegistryWrites_get,
                List.foldl_cons, List.foldl_nil]
              simp [Ne.symm htail.2.1, Ne.symm hlength.2.1, htargetIndex,
                oneBasedIndexAt_swapPop_moved_of_lt_last
                  entries hfind hw.targetsNodup hlast hnonself]
            · have hlastIndex : indexSlot last.1 ≠ indexSlot wanted := by
                intro hslots
                exact (Ne.symm hlastEq)
                  (indexSlot_injective hlastTarget.2 hwanted hslots)
              simp only [logicalStorageOfStor, applyRegistryWrites_get,
                List.foldl_cons, List.foldl_nil]
              simp [hassignmentPair.1, Ne.symm hassignmentPair.2.2,
                Ne.symm hhole.2.1, hlastIndex, Ne.symm htail.2.1,
                Ne.symm hlength.2.1, htargetIndex]
              rw [oneBasedIndexAt_swapPop_of_findEntry_ne_last
                hfind hwantedFind hw.targetsNodup hlast htargetEq hlastEq]
              simpa [logicalStorageOfStor, findEntry_oneBasedIndexAt hwantedFind]
                using hw.indices wanted hwanted
    counts := by
      intro wanted hwanted
      have hassignment :=
        registryAddressFamilies_pairwise htarget.2 htarget.2 hwanted
      have hhole :=
        registryAddressFamilies_ne_arrayEntrySlot htarget.2 hwanted hindex252
      have hlastIndex :=
        registryAddressFamilies_pairwise htarget.2 hlastTarget.2 hwanted
      have htail :=
        registryAddressFamilies_ne_arrayEntrySlot htarget.2 hwanted hlength252
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot htarget.2 hwanted
      by_cases heq : wanted = oldPauser
      · subst wanted
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [hassignment.2.2, Ne.symm hhole.2.2,
          hlastIndex.2.2, Ne.symm htail.2.2, Ne.symm hlength.2.2,
          assignmentCount_swapPop_of_findEntry hfind]
      · have hcount : countSlot oldPauser ≠ countSlot wanted := by
          intro hslots
          exact (Ne.symm heq)
            (countSlot_injective hold.2 hwanted hslots)
        simp only [logicalStorageOfStor, applyRegistryWrites_get,
          List.foldl_cons, List.foldl_nil]
        simp [hassignment.2.1, hassignment.2.2, hcount,
          Ne.symm hhole.2.2, hlastIndex.2.2,
          Ne.symm htail.2.2, Ne.symm hlength.2.2]
        rw [assignmentCount_swapPop_of_findEntry hfind]
        simp [Ne.symm heq]
        simpa [logicalStorageOfStor] using hw.counts wanted hwanted
    zeroCount := by
      have hzeroCanonical : canonicalAddress (0 : B256) := by
        unfold canonicalAddress
        change (0 : Nat) < 2 ^ 160
        norm_num
      have hassignment :=
        registryAddressFamilies_pairwise htarget.2 htarget.2 hzeroCanonical
      have hcount : countSlot oldPauser ≠ countSlot 0 := by
        intro hslots
        exact hold.1 (countSlot_injective hold.2 hzeroCanonical hslots)
      have hhole :=
        registryAddressFamilies_ne_arrayEntrySlot
          htarget.2 hzeroCanonical hindex252
      have hlastIndex :=
        registryAddressFamilies_pairwise htarget.2 hlastTarget.2 hzeroCanonical
      have htail :=
        registryAddressFamilies_ne_arrayEntrySlot
          htarget.2 hzeroCanonical hlength252
      have hlength :=
        registryAddressFamilies_ne_arrayLengthSlot htarget.2 hzeroCanonical
      simp only [logicalStorageOfStor, applyRegistryWrites_get,
        List.foldl_cons, List.foldl_nil]
      simp [hassignment.2.1, hassignment.2.2, hcount,
        Ne.symm hhole.2.2, hlastIndex.2.2,
        Ne.symm htail.2.2, Ne.symm hlength.2.2]
      simpa [logicalStorageOfStor] using hw.zeroCount
  }

/-- The stable model poststate and complete preceding Registry-write chronology. -/
structure SetPauserSourceTrace where
  postEntries : List Entry
  writes : List RegistryWrite

/-- Exact logical Registry SSTORE chronology of `setPauserKernel` through its
final Registry store.  The zero target rejects before any own Registry write. -/
def setPauserSourceWrites (entries : List Entry) (target newPauser : B256) :
    Option (List RegistryWrite) :=
  if target = 0 then none
  else match findEntry entries target with
    | none =>
        let len := entries.length
        let next := Nat.toB256 (len + 1)
        let assignment := (assignmentSlot target, newPauser)
        let appendWrites :=
          [(arrayEntrySlot next, target), (indexSlot target, next),
            (arrayLengthSlot, next)]
        if newPauser = 0 then
          some (assignment :: appendWrites ++
            [(arrayEntrySlot next, target), (indexSlot target, next),
              (arrayEntrySlot next, 0), (arrayLengthSlot, Nat.toB256 len),
              (indexSlot target, 0)])
        else
          some (assignment :: appendWrites ++
            [(countSlot newPauser,
              Nat.toB256 (assignmentCount entries newPauser + 1))])
    | some (index, oldPauser) =>
        let indexWord := Nat.toB256 (index + 1)
        let lengthWord := Nat.toB256 entries.length
        let assignment := (assignmentSlot target, newPauser)
        let oldCount :=
          (countSlot oldPauser,
            Nat.toB256 (assignmentCount entries oldPauser - 1))
        if newPauser = 0 then
          let lastTarget := sourceLastTarget entries
          some [assignment, oldCount,
            (arrayEntrySlot indexWord, lastTarget),
            (indexSlot lastTarget, indexWord),
            (arrayEntrySlot lengthWord, 0),
            (arrayLengthSlot, Nat.toB256 (entries.length - 1)),
            (indexSlot target, 0)]
        else
          some [assignment, oldCount,
            (countSlot newPauser,
              Nat.toB256
                ((assignmentCount entries newPauser -
                  (if oldPauser = newPauser then 1 else 0)) + 1))]

/-- Pair the independently computed write chronology with the pure model's
stable poststate. -/
def setPauserSourceTrace (entries : List Entry) (target newPauser : B256) :
    Option SetPauserSourceTrace :=
  match setPauser entries target newPauser with
  | none => none
  | some postEntries =>
      let writes := Option.getD (setPauserSourceWrites entries target newPauser) []
      some { postEntries, writes }

theorem setPauserSourceTrace_postEntries
    (entries : List Entry) (target newPauser : B256) :
    Option.map SetPauserSourceTrace.postEntries
      (setPauserSourceTrace entries target newPauser) =
      setPauser entries target newPauser := by
  cases h : setPauser entries target newPauser <;>
    simp [setPauserSourceTrace, h]

theorem setPauserSourceWrites_target_zero
    (entries : List Entry) (newPauser : B256) :
    setPauserSourceWrites entries 0 newPauser = none := by
  simp [setPauserSourceWrites]

theorem setPauserSourceTrace_target_zero
    (entries : List Entry) (newPauser : B256) :
    setPauserSourceTrace entries 0 newPauser = none := by
  simp [setPauserSourceTrace, setPauser]

theorem setPauserSourceWrites_fresh_nonzero
    (entries : List Entry) (target newPauser : B256)
    (htarget : target ≠ 0) (hfind : findEntry entries target = none)
    (hnew : newPauser ≠ 0) :
    setPauserSourceWrites entries target newPauser =
      some [(assignmentSlot target, newPauser),
        (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
        (indexSlot target, Nat.toB256 (entries.length + 1)),
        (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
        (countSlot newPauser,
          Nat.toB256 (assignmentCount entries newPauser + 1))] := by
  simp [setPauserSourceWrites, htarget, hfind, hnew]

theorem setPauserSourceWrites_absent_zero
    (entries : List Entry) (target : B256)
    (htarget : target ≠ 0) (hfind : findEntry entries target = none) :
    setPauserSourceWrites entries target 0 =
      some [(assignmentSlot target, 0),
        (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
        (indexSlot target, Nat.toB256 (entries.length + 1)),
        (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
        (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
        (indexSlot target, Nat.toB256 (entries.length + 1)),
        (arrayEntrySlot (Nat.toB256 (entries.length + 1)), 0),
        (arrayLengthSlot, Nat.toB256 entries.length),
        (indexSlot target, 0)] := by
  simp [setPauserSourceWrites, htarget, hfind]

theorem setPauserSourceWrites_found_zero
    (entries : List Entry) (target : B256) (index : Nat)
    (oldPauser : B256)
    (htarget : target ≠ 0)
    (hfind : findEntry entries target = some (index, oldPauser)) :
    setPauserSourceWrites entries target 0 =
      some [(assignmentSlot target, 0),
        (countSlot oldPauser,
          Nat.toB256 (assignmentCount entries oldPauser - 1)),
        (arrayEntrySlot (Nat.toB256 (index + 1)), sourceLastTarget entries),
        (indexSlot (sourceLastTarget entries), Nat.toB256 (index + 1)),
        (arrayEntrySlot (Nat.toB256 entries.length), 0),
        (arrayLengthSlot, Nat.toB256 (entries.length - 1)),
        (indexSlot target, 0)] := by
  simp [setPauserSourceWrites, htarget, hfind]

theorem setPauserSourceWrites_found_nonzero
    (entries : List Entry) (target newPauser : B256) (index : Nat)
    (oldPauser : B256)
    (htarget : target ≠ 0)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hnew : newPauser ≠ 0) :
    setPauserSourceWrites entries target newPauser =
      some [(assignmentSlot target, newPauser),
        (countSlot oldPauser,
          Nat.toB256 (assignmentCount entries oldPauser - 1)),
        (countSlot newPauser,
          Nat.toB256
            ((assignmentCount entries newPauser -
              (if oldPauser = newPauser then 1 else 0)) + 1))] := by
  simp [setPauserSourceWrites, htarget, hfind, hnew]

theorem setPauserSourceTrace_writes
    (entries : List Entry) (target newPauser : B256) :
    Option.map SetPauserSourceTrace.writes
      (setPauserSourceTrace entries target newPauser) =
      setPauserSourceWrites entries target newPauser := by
  by_cases htarget : target = 0
  · simp [setPauserSourceTrace, setPauserSourceWrites, setPauser, htarget]
  · cases hfind : findEntry entries target <;>
      by_cases hnew : newPauser = 0 <;>
      simp [setPauserSourceTrace, setPauserSourceWrites, setPauser,
        htarget, hfind, hnew]

theorem setPauser_sourceTrace_refines_model {entries target newPauser}
    (htarget0 : target ≠ 0) {trace}
    (htrace : setPauserSourceTrace entries target newPauser = some trace) :
    setPauser entries target newPauser = some trace.postEntries ∧
      setPauserSourceWrites entries target newPauser = some trace.writes := by
  cases hfind : findEntry entries target <;>
    by_cases hnew : newPauser = 0 <;>
    simp [setPauserSourceTrace, setPauserSourceWrites, setPauser,
      htarget0, hfind, hnew] at htrace
  all_goals cases htrace
  all_goals simp [setPauser, setPauserSourceWrites, htarget0, hfind, hnew]

private theorem oneBasedIndexAt_ne_zero_of_mem
    {entries : List Entry} {target : B256}
    (hmem : target ∈ entries.map Prod.fst) :
    oneBasedIndexAt entries target ≠ 0 := by
  induction entries with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons] at hmem
      by_cases hhead : entry.1 = target
      · simp [oneBasedIndexAt, hhead]
      · have hrest : target ∈ rest.map Prod.fst := by
          rcases hmem with heq | hmem
          · exact (hhead heq.symm).elim
          · exact hmem
        simp [oneBasedIndexAt, hhead, ih hrest]

/-- Setting a nonzero target's pauser to zero removes the target from the
model, so both lookup projections become zero. -/
theorem setPauser_zero_removes
    {entries postEntries : List Entry} {target : B256}
    (hnodup : (entries.map Prod.fst).Nodup)
    (htarget : target ≠ 0)
    (hset : setPauser entries target 0 = some postEntries) :
    target ∉ postEntries.map Prod.fst ∧
    assignmentAt postEntries target = 0 ∧
    oneBasedIndexAt postEntries target = 0 := by
  cases hfind : findEntry entries target with
  | none =>
      simp [setPauser, htarget, hfind] at hset
      subst postEntries
      exact ⟨findEntry_none_target_not_mem_targets hfind,
        findEntry_none_assignmentAt hfind,
        findEntry_none_oneBasedIndexAt hfind⟩
  | some found =>
      obtain ⟨index, oldPauser⟩ := found
      simp [setPauser, htarget, hfind] at hset
      subst postEntries
      have hindex :=
        oneBasedIndexAt_swapPop_target_of_findEntry hfind hnodup
      exact ⟨fun hmem => oneBasedIndexAt_ne_zero_of_mem hmem hindex,
        assignmentAt_swapPop_target_of_findEntry hfind hnodup,
        hindex⟩

/-- Every successful source-level Registry trace preserves the combined
logical witness after replaying its exact chronological Registry writes. -/
theorem RegistryWitness.applySetPauserSourceTrace
    {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    {target newPauser : B256}
    (htarget : canonicalAddress target)
    (hnew : canonicalAddress newPauser)
    {trace : SetPauserSourceTrace}
    (htrace : setPauserSourceTrace entries target newPauser = some trace) :
    RegistryWitness
      (logicalStorageOfStor (applyRegistryWrites s trace.writes))
      trace.postEntries := by
  by_cases htarget0 : target = 0
  · subst target
    simp [setPauserSourceTrace_target_zero] at htrace
  · have htargetValid : nonzeroCanonicalAddress target :=
      ⟨htarget0, htarget⟩
    cases hfind : findEntry entries target with
    | none =>
        by_cases hnew0 : newPauser = 0
        · subst newPauser
          simp [setPauserSourceTrace, setPauserSourceWrites, setPauser,
            htarget0, hfind] at htrace
          cases htrace
          exact hw.applyAbsentZeroWrites htargetValid hfind
        · have hnewValid : nonzeroCanonicalAddress newPauser :=
            ⟨hnew0, hnew⟩
          simp [setPauserSourceTrace, setPauserSourceWrites, setPauser,
            htarget0, hfind, hnew0] at htrace
          cases htrace
          exact hw.applyFreshWrites htargetValid hnewValid hfind
    | some found =>
        obtain ⟨index, oldPauser⟩ := found
        by_cases hnew0 : newPauser = 0
        · subst newPauser
          simp [setPauserSourceTrace, setPauserSourceWrites, setPauser,
            htarget0, hfind] at htrace
          cases htrace
          exact hw.applyFoundZeroWrites htargetValid hfind
        · have hnewValid : nonzeroCanonicalAddress newPauser :=
            ⟨hnew0, hnew⟩
          simp [setPauserSourceTrace, setPauserSourceWrites, setPauser,
            htarget0, hfind, hnew0] at htrace
          cases htrace
          exact hw.applyFoundNonzeroWrites htargetValid hnewValid hfind

/-- A successful source run reaches the boundary immediately after its final
Registry SSTORE with exactly the model trace's chronological writes applied. -/
theorem setPauser_run_extracts_sourceTrace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {entries : List Entry} {target newPauser : B256}
    {continuation : B256} {ca : Adr} {trace : SetPauserSourceTrace}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (howner : sevm.currentTarget = ca)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htargetCanonical : canonicalAddress target)
    (hnewCanonical : canonicalAddress newPauser)
    (herrorLookup : fs[pausableZeroErrorSlot]? = some pausableZeroError)
    (happendLookup : fs[appendTargetSlot]? = some appendTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hrun : Func.Run fs sevm pre setPauserKernel final)
    (htrace : setPauserSourceTrace entries target newPauser = some trace) :
    ∃ postRegistry postImg,
      Mem.Wf postRegistry.memory ∧
      Mem.Reads postRegistry.memory postImg ∧
      Bytes.toB256
        (postImg.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Bytes.toB256
        (postImg.sliceD (newPauserWord * 32).toNat 32 0) = newPauser ∧
      Bytes.toB256
        (postImg.sliceD (previousPauserWord * 32).toNat 32 0) =
          assignmentAt entries target ∧
      Bytes.toB256
        (postImg.sliceD (continuationWord * 32).toNat 32 0) =
          continuation ∧
      Devm.getStor postRegistry ca =
        applyRegistryWrites (Devm.getStor pre ca) trace.writes ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor postRegistry ca))
        trace.postEntries ∧
      Devm.getCode pre = Devm.getCode postRegistry ∧
      Func.Run fs sevm postRegistry finishSetPauser final := by
  rcases setPauser_run_extracts_nonzero_guard
      hwf hr htargetRead herrorLookup hrun with
    ⟨htarget0, guardPre, hguardStack, hwfGuard, hrGuard,
      hstorGuard, hcodeGuard, hguardRun⟩
  have htarget : nonzeroCanonicalAddress target :=
    ⟨htarget0, htargetCanonical⟩
  have hwGuard : RegistryWitness
      (logicalStorageOfStor (Devm.getStor guardPre ca)) entries := by
    rw [← congrFun hstorGuard ca]
    exact hw
  rcases setPauser_run_extracts_assignment_write
      hguardStack hwfGuard hrGuard htargetRead hnewRead howner hwGuard
      htarget hnewCanonical hguardRun with
    ⟨oldPauser, postAssign, holdPauser, hassignStack, hwfAssign,
      hrAssign, hstorAssign, hcodeAssign, hassignRun⟩
  have hcodeToAssign : Devm.getCode pre = Devm.getCode postAssign :=
    hcodeGuard.trans hcodeAssign
  let imgPrev := Bytes.writeAt img (previousPauserWord * 32).toNat
    oldPauser.toBytes
  have htargetPrev : Bytes.toB256
      (imgPrev.sliceD (targetWord * 32).toNat 32 0) = target := by
    have hoff : (targetWord * 32).toNat + 32 ≤
        (previousPauserWord * 32).toNat := by decide
    dsimp [imgPrev]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
    exact htargetRead
  have hnewPrev : Bytes.toB256
      (imgPrev.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    have hoff : (newPauserWord * 32).toNat + 32 ≤
        (previousPauserWord * 32).toNat := by decide
    dsimp [imgPrev]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
    exact hnewRead
  have hpreviousPrev : Bytes.toB256
      (imgPrev.sliceD (previousPauserWord * 32).toNat 32 0) =
        assignmentAt entries target := by
    dsimp [imgPrev]
    rw [show 32 = oldPauser.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes, holdPauser]
  have hcontinuationPrev : Bytes.toB256
      (imgPrev.sliceD (continuationWord * 32).toNat 32 0) =
        continuation := by
    dsimp [imgPrev]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _
      (by rw [B256.length_toBytes]; decide)]
    exact hcontinuationRead
  rcases setPauser_run_split_old_assignment
      hassignStack hwfAssign hrAssign hassignRun with
    holdZero | holdNonzero
  · rcases holdZero with
      ⟨holdZero, appendCallPre, happendStack, hwfAppendCall,
        hrAppendCall, hstorAppendCall, hcodeAppendCall, happendCallRun⟩
    cases hfind : findEntry entries target with
    | some found =>
        obtain ⟨index, foundPauser⟩ := found
        have hfound := findEntry_assignmentAt hfind
        have hfoundValid :=
          hw.pausersValid (target, foundPauser) (mem_of_findEntry hfind)
        have hfoundZero : foundPauser = 0 := by
          calc
            foundPauser = assignmentAt entries target := hfound.symm
            _ = oldPauser := holdPauser.symm
            _ = 0 := holdZero
        exact (hfoundValid.1 hfoundZero).elim
    | none =>
        rcases of_run_call happendCallRun with
          ⟨appendBody, appendPre, happendGet, happendBurn,
            happendBodyRun⟩
        rw [happendLookup] at happendGet
        have happendEq : appendTarget = appendBody :=
          Option.some.inj happendGet
        rw [← happendEq] at happendBodyRun
        have happendBodyStack : pre.stack <<+ appendPre.stack := by
          rw [← happendBurn.stack]
          exact happendStack
        have hwfAppend : Mem.Wf appendPre.memory := by
          rw [← happendBurn.memory]
          exact hwfAppendCall
        have hrAppend : Mem.Reads appendPre.memory imgPrev := by
          rw [← happendBurn.memory]
          exact hrAppendCall
        have hstorAppend : Devm.getStor appendPre ca =
            (Devm.getStor guardPre ca).set
              (assignmentSlot target) newPauser := by
          calc
            Devm.getStor appendPre ca =
                Devm.getStor appendCallPre ca :=
              congrFun (Burn.Inv.inv happendBurn).symm ca
            _ = Devm.getStor postAssign ca :=
              congrFun hstorAppendCall.symm ca
            _ = (Devm.getStor guardPre ca).set
                (assignmentSlot target) newPauser := hstorAssign
        rcases appendTarget_run_extracts_writes
            happendBodyStack hwfAppend hrAppend htargetPrev howner hwGuard
            hstorAppend htarget hafterLookup happendBodyRun with
          ⟨postAppend, hpostAppendStack, hwfPostAppend, hrPostAppend,
            hstorPostAppend, hcodeAppend, hafterRun⟩
        have hcodeToMid : Devm.getCode pre = Devm.getCode postAppend :=
          hcodeToAssign.trans (hcodeAppendCall.trans
            ((getCode_of_state_eq happendBurn.state).trans hcodeAppend))
        let entryStor := Devm.getStor guardPre ca
        let imgNext := Bytes.writeAt imgPrev
          (arrayLengthWord * 32).toNat
          (Nat.toB256 (entries.length + 1)).toBytes
        have htargetNext : Bytes.toB256
            (imgNext.sliceD (targetWord * 32).toNat 32 0) = target := by
          have hoff : (targetWord * 32).toNat + 32 ≤
              (arrayLengthWord * 32).toNat := by decide
          dsimp [imgNext]
          rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
          exact htargetPrev
        have hnewNext : Bytes.toB256
            (imgNext.sliceD (newPauserWord * 32).toNat 32 0) =
              newPauser := by
          have hoff : (newPauserWord * 32).toNat + 32 ≤
              (arrayLengthWord * 32).toNat := by decide
          dsimp [imgNext]
          rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
          exact hnewPrev
        have hpreviousNext : Bytes.toB256
            (imgNext.sliceD (previousPauserWord * 32).toNat 32 0) =
              assignmentAt entries target := by
          have hoff : (previousPauserWord * 32).toNat + 32 ≤
              (arrayLengthWord * 32).toNat := by decide
          dsimp [imgNext]
          rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
          exact hpreviousPrev
        have hcontinuationNext : Bytes.toB256
            (imgNext.sliceD (continuationWord * 32).toNat 32 0) =
              continuation := by
          have hoff : (continuationWord * 32).toNat + 32 ≤
              (arrayLengthWord * 32).toNat := by decide
          dsimp [imgNext]
          rw [Bytes.sliceD_writeAt_before _ _ _ _ _ hoff]
          exact hcontinuationPrev
        rcases afterOldPauser_run_split_new_assignment
            hpostAppendStack hwfPostAppend hrPostAppend hnewNext hafterRun with
          hnewZero | hnewNonzero
        · rcases hnewZero with
            ⟨hnewZero, removeCallPre, hremoveStack, hwfRemoveCall,
              hrRemoveCall, hstorRemoveCall, hcodeRemoveCall,
              hremoveCallRun⟩
          rcases of_run_call hremoveCallRun with
            ⟨removeBody, removePre, hremoveGet, hremoveBurn,
              hremoveBodyRun⟩
          rw [hremoveLookup] at hremoveGet
          have hremoveEq : removeTarget = removeBody :=
            Option.some.inj hremoveGet
          rw [← hremoveEq] at hremoveBodyRun
          have hremoveBodyStack :
              Nat.toB256 (entries.length + 1) :: pre.stack <<+
                removePre.stack := by
            rw [← hremoveBurn.stack]
            exact hremoveStack
          have hwfRemove : Mem.Wf removePre.memory := by
            rw [← hremoveBurn.memory]
            exact hwfRemoveCall
          have hrRemove : Mem.Reads removePre.memory imgNext := by
            rw [← hremoveBurn.memory]
            exact hrRemoveCall
          have hstorRemove : Devm.getStor removePre ca =
              (((entryStor.set
                (assignmentSlot target) newPauser).set
                (arrayEntrySlot (Nat.toB256 (entries.length + 1)))
                  target).set
                (indexSlot target) (Nat.toB256 (entries.length + 1))).set
                arrayLengthSlot (Nat.toB256 (entries.length + 1)) := by
            calc
              Devm.getStor removePre ca = Devm.getStor removeCallPre ca :=
                congrFun (Burn.Inv.inv hremoveBurn).symm ca
              _ = Devm.getStor postAppend ca :=
                congrFun hstorRemoveCall.symm ca
              _ = _ := by simpa [entryStor] using hstorPostAppend
          have hreads := appendedRegistryStorage_reads
            hwGuard htarget hnewCanonical
          rcases removeTarget_run_extracts_writes
              hremoveBodyStack hwfRemove hrRemove htargetNext howner
              hstorRemove hreads.1 hreads.2.1 hreads.2.2.1
              hreads.2.2.2.2 hfinishLookup hremoveBodyRun with
            ⟨postRegistry, _, hwfPost, hrPost, hstorPostRegistry,
              hcodePostRegistry, hfinishRun⟩
          let postImg := Bytes.writeAt
            (Bytes.writeAt
              (Bytes.writeAt imgNext (removedIndexWord * 32).toNat
                (Nat.toB256 (entries.length + 1)).toBytes)
              (arrayLengthWord * 32).toNat
                (Nat.toB256 (entries.length + 1)).toBytes)
            (lastTargetWord * 32).toNat target.toBytes
          have htargetPost : Bytes.toB256
              (postImg.sliceD (targetWord * 32).toNat 32 0) = target := by
            dsimp [postImg]
            rw [removeImage_sliceD _ _ _ _ _ _
              (by decide) (by decide) (by decide)]
            exact htargetNext
          have hnewPost : Bytes.toB256
              (postImg.sliceD (newPauserWord * 32).toNat 32 0) =
                newPauser := by
            dsimp [postImg]
            rw [removeImage_sliceD _ _ _ _ _ _
              (by decide) (by decide) (by decide)]
            exact hnewNext
          have hpreviousPost : Bytes.toB256
              (postImg.sliceD (previousPauserWord * 32).toNat 32 0) =
                assignmentAt entries target := by
            dsimp [postImg]
            rw [removeImage_sliceD _ _ _ _ _ _
              (by decide) (by decide) (by decide)]
            exact hpreviousNext
          have hcontinuationPost : Bytes.toB256
              (postImg.sliceD (continuationWord * 32).toNat 32 0) =
                continuation := by
            dsimp [postImg]
            rw [removeImage_sliceD _ _ _ _ _ _
              (by decide) (by decide) (by decide)]
            exact hcontinuationNext
          have hwrites :=
            (setPauser_sourceTrace_refines_model htarget0 htrace).2
          rw [hnewZero,
            setPauserSourceWrites_absent_zero entries target htarget0 hfind]
              at hwrites
          have hwritesEq := Option.some.inj hwrites
          have hpostStor : Devm.getStor postRegistry ca =
              applyRegistryWrites (Devm.getStor pre ca) trace.writes := by
            rw [← hwritesEq]
            simp only [applyRegistryWrites, List.foldl_cons, List.foldl_nil]
            rw [hstorPostRegistry]
            dsimp [entryStor]
            rw [hnewZero, ← congrFun hstorGuard ca]
          refine ⟨postRegistry, postImg, hwfPost, hrPost, htargetPost,
            hnewPost, hpreviousPost, hcontinuationPost, hpostStor, ?_,
            hcodeToMid.trans (hcodeRemoveCall.trans
              ((getCode_of_state_eq hremoveBurn.state).trans
                hcodePostRegistry)),
            hfinishRun⟩
          rw [hpostStor]
          exact hw.applySetPauserSourceTrace
            htargetCanonical hnewCanonical htrace
        · rcases hnewNonzero with
            ⟨hnew0, newCountPre, hnewCountStack, hwfNewCount,
              hrNewCount, hstorNewCount, hcodeNewCount, hnewCountRun⟩
          have hnew : nonzeroCanonicalAddress newPauser :=
            ⟨hnew0, hnewCanonical⟩
          have hreads := appendedRegistryStorage_reads hwGuard htarget hnew.2
          have hcurrent : Devm.getStor newCountPre ca =
              (((entryStor.set
                (assignmentSlot target) newPauser).set
                (arrayEntrySlot (Nat.toB256 (entries.length + 1)))
                  target).set
                (indexSlot target) (Nat.toB256 (entries.length + 1))).set
                arrayLengthSlot (Nat.toB256 (entries.length + 1)) := by
            exact (congrFun hstorNewCount ca).symm.trans
              (by simpa [entryStor] using hstorPostAppend)
          rcases afterOldPauser_run_extracts_new_count_write
              hnewCountStack hwfNewCount hrNewCount hnewNext howner
              hcurrent hreads.2.2.2.1
              (hwGuard.assignmentCountWord_succ_eq_add_one newPauser)
              hfinishLookup hnewCountRun with
            ⟨postRegistry, _, hwfPost, hrPost, hstorPostRegistry,
              hcodePostRegistry, hfinishRun⟩
          have hwrites :=
            (setPauser_sourceTrace_refines_model htarget0 htrace).2
          rw [setPauserSourceWrites_fresh_nonzero entries target newPauser
            htarget0 hfind hnew0] at hwrites
          have hwritesEq := Option.some.inj hwrites
          have hpostStor : Devm.getStor postRegistry ca =
              applyRegistryWrites (Devm.getStor pre ca) trace.writes := by
            rw [← hwritesEq]
            simp only [applyRegistryWrites, List.foldl_cons, List.foldl_nil]
            rw [hstorPostRegistry]
            dsimp [entryStor]
            rw [← congrFun hstorGuard ca]
          refine ⟨postRegistry, imgNext, hwfPost, hrPost, htargetNext,
            hnewNext, hpreviousNext, hcontinuationNext, hpostStor, ?_,
            hcodeToMid.trans (hcodeNewCount.trans hcodePostRegistry),
            hfinishRun⟩
          rw [hpostStor]
          exact hw.applySetPauserSourceTrace
            htargetCanonical hnewCanonical htrace
  · rcases holdNonzero with
      ⟨holdNonzero, oldCountPre, holdCountStack, hwfOldCount,
        hrOldCount, hstorOldCount, hcodeOldCount, holdCountRun⟩
    cases hfind : findEntry entries target with
    | none =>
        have holdZero : oldPauser = 0 :=
          holdPauser.trans (findEntry_none_assignmentAt hfind)
        exact (holdNonzero holdZero).elim
    | some found =>
        obtain ⟨index, foundPauser⟩ := found
        have holdFound : oldPauser = foundPauser :=
          holdPauser.trans (findEntry_assignmentAt hfind)
        rw [← holdFound] at hfind
        have hprevPrev : Bytes.toB256
            (imgPrev.sliceD (previousPauserWord * 32).toNat 32 0) =
              oldPauser := by
          dsimp [imgPrev]
          rw [show 32 = oldPauser.toBytes.length by
            rw [B256.length_toBytes]]
          rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
        have hstorOld : Devm.getStor oldCountPre ca =
            (Devm.getStor guardPre ca).set
              (assignmentSlot target) newPauser := by
          calc
            Devm.getStor oldCountPre ca = Devm.getStor postAssign ca :=
              congrFun hstorOldCount.symm ca
            _ = _ := hstorAssign
        rcases setPauser_run_extracts_old_count_write
            holdCountStack hwfOldCount hrOldCount hprevPrev howner hwGuard
            htarget hfind hstorOld holdCountRun with
          ⟨postOld, hpostOldStack, hwfPostOld, hrPostOld,
            hstorPostOld, hcodeOld, hafterCallRun⟩
        rcases of_run_call hafterCallRun with
          ⟨afterBody, afterPre, hafterGet, hafterBurn, hafterBodyRun⟩
        rw [hafterLookup] at hafterGet
        have hafterEq : afterOldPauser = afterBody :=
          Option.some.inj hafterGet
        rw [← hafterEq] at hafterBodyRun
        have hafterStack : pre.stack <<+ afterPre.stack := by
          rw [← hafterBurn.stack]
          exact hpostOldStack
        have hwfAfter : Mem.Wf afterPre.memory := by
          rw [← hafterBurn.memory]
          exact hwfPostOld
        have hrAfter : Mem.Reads afterPre.memory imgPrev := by
          rw [← hafterBurn.memory]
          exact hrPostOld
        have hcodeToMid : Devm.getCode pre = Devm.getCode afterPre :=
          hcodeToAssign.trans (hcodeOldCount.trans
            (hcodeOld.trans (getCode_of_state_eq hafterBurn.state)))
        rcases afterOldPauser_run_split_new_assignment
            hafterStack hwfAfter hrAfter hnewPrev hafterBodyRun with
          hnewZero | hnewNonzero
        · rcases hnewZero with
            ⟨hnewZero, removeCallPre, hremoveStack, hwfRemoveCall,
              hrRemoveCall, hstorRemoveCall, hcodeRemoveCall,
              hremoveCallRun⟩
          rcases of_run_call hremoveCallRun with
            ⟨removeBody, removePre, hremoveGet, hremoveBurn,
              hremoveBodyRun⟩
          rw [hremoveLookup] at hremoveGet
          have hremoveEq : removeTarget = removeBody :=
            Option.some.inj hremoveGet
          rw [← hremoveEq] at hremoveBodyRun
          have hremoveBodyStack : pre.stack <<+ removePre.stack := by
            rw [← hremoveBurn.stack]
            exact hremoveStack
          have hwfRemove : Mem.Wf removePre.memory := by
            rw [← hremoveBurn.memory]
            exact hwfRemoveCall
          have hrRemove : Mem.Reads removePre.memory imgPrev := by
            rw [← hremoveBurn.memory]
            exact hrRemoveCall
          have hcurrent : Devm.getStor removePre ca =
              ((Devm.getStor guardPre ca).set
                (assignmentSlot target) 0).set
                (countSlot oldPauser)
                (Nat.toB256 (assignmentCount entries oldPauser - 1)) := by
            calc
              Devm.getStor removePre ca = Devm.getStor removeCallPre ca :=
                congrFun (Burn.Inv.inv hremoveBurn).symm ca
              _ = Devm.getStor afterPre ca :=
                congrFun hstorRemoveCall.symm ca
              _ = Devm.getStor postOld ca :=
                congrFun (Burn.Inv.inv hafterBurn).symm ca
              _ = ((Devm.getStor guardPre ca).set
                    (assignmentSlot target) newPauser).set
                    (countSlot oldPauser)
                    (Nat.toB256
                      (assignmentCount entries oldPauser - 1)) :=
                hstorPostOld
              _ = _ := by rw [hnewZero]
          have hreads := foundRemovalStorage_reads hwGuard htarget hfind
          rcases removeTarget_run_extracts_writes
              hremoveBodyStack hwfRemove hrRemove htargetPrev howner
              hcurrent hreads.1 hreads.2.1 hreads.2.2.1
              hreads.2.2.2 hfinishLookup hremoveBodyRun with
            ⟨postRegistry, _, hwfPost, hrPost, hstorPostRegistry,
              hcodePostRegistry, hfinishRun⟩
          let postImg := Bytes.writeAt
            (Bytes.writeAt
              (Bytes.writeAt imgPrev (removedIndexWord * 32).toNat
                (Nat.toB256 (index + 1)).toBytes)
              (arrayLengthWord * 32).toNat
                (Nat.toB256 entries.length).toBytes)
            (lastTargetWord * 32).toNat
              (sourceLastTarget entries).toBytes
          have htargetPost : Bytes.toB256
              (postImg.sliceD (targetWord * 32).toNat 32 0) = target := by
            dsimp [postImg]
            rw [removeImage_sliceD _ _ _ _ _ _
              (by decide) (by decide) (by decide)]
            exact htargetPrev
          have hnewPost : Bytes.toB256
              (postImg.sliceD (newPauserWord * 32).toNat 32 0) =
                newPauser := by
            dsimp [postImg]
            rw [removeImage_sliceD _ _ _ _ _ _
              (by decide) (by decide) (by decide)]
            exact hnewPrev
          have hpreviousPost : Bytes.toB256
              (postImg.sliceD (previousPauserWord * 32).toNat 32 0) =
                assignmentAt entries target := by
            dsimp [postImg]
            rw [removeImage_sliceD _ _ _ _ _ _
              (by decide) (by decide) (by decide)]
            exact hpreviousPrev
          have hcontinuationPost : Bytes.toB256
              (postImg.sliceD (continuationWord * 32).toNat 32 0) =
                continuation := by
            dsimp [postImg]
            rw [removeImage_sliceD _ _ _ _ _ _
              (by decide) (by decide) (by decide)]
            exact hcontinuationPrev
          have hwrites :=
            (setPauser_sourceTrace_refines_model htarget0 htrace).2
          rw [hnewZero,
            setPauserSourceWrites_found_zero entries target index oldPauser
              htarget0 hfind] at hwrites
          have hwritesEq := Option.some.inj hwrites
          have hpostStor : Devm.getStor postRegistry ca =
              applyRegistryWrites (Devm.getStor pre ca) trace.writes := by
            rw [← hwritesEq]
            simp only [applyRegistryWrites, List.foldl_cons, List.foldl_nil]
            rw [hstorPostRegistry, ← congrFun hstorGuard ca]
          refine ⟨postRegistry, postImg, hwfPost, hrPost, htargetPost,
            hnewPost, hpreviousPost, hcontinuationPost, hpostStor, ?_,
            hcodeToMid.trans (hcodeRemoveCall.trans
              ((getCode_of_state_eq hremoveBurn.state).trans
                hcodePostRegistry)),
            hfinishRun⟩
          rw [hpostStor]
          exact hw.applySetPauserSourceTrace
            htargetCanonical hnewCanonical htrace
        · rcases hnewNonzero with
            ⟨hnew0, newCountPre, hnewCountStack, hwfNewCount,
              hrNewCount, hstorNewCount, hcodeNewCount, hnewCountRun⟩
          have hnew : nonzeroCanonicalAddress newPauser :=
            ⟨hnew0, hnewCanonical⟩
          have hcurrent : Devm.getStor newCountPre ca =
              ((Devm.getStor guardPre ca).set
                (assignmentSlot target) newPauser).set
                (countSlot oldPauser)
                (Nat.toB256 (assignmentCount entries oldPauser - 1)) := by
            calc
              Devm.getStor newCountPre ca = Devm.getStor afterPre ca :=
                congrFun hstorNewCount.symm ca
              _ = Devm.getStor postOld ca :=
                congrFun (Burn.Inv.inv hafterBurn).symm ca
              _ = _ := hstorPostOld
          have hreads := reassignedRegistryStorage_newCount
            hwGuard htarget hnew hfind
          rcases afterOldPauser_run_extracts_new_count_write
              hnewCountStack hwfNewCount hrNewCount hnewPrev howner
              hcurrent hreads.1 hreads.2 hfinishLookup hnewCountRun with
            ⟨postRegistry, _, hwfPost, hrPost, hstorPostRegistry,
              hcodePostRegistry, hfinishRun⟩
          have hwrites :=
            (setPauser_sourceTrace_refines_model htarget0 htrace).2
          rw [setPauserSourceWrites_found_nonzero entries target newPauser
            index oldPauser htarget0 hfind hnew0] at hwrites
          have hwritesEq := Option.some.inj hwrites
          have hpostStor : Devm.getStor postRegistry ca =
              applyRegistryWrites (Devm.getStor pre ca) trace.writes := by
            rw [← hwritesEq]
            simp only [applyRegistryWrites, List.foldl_cons, List.foldl_nil]
            rw [hstorPostRegistry, ← congrFun hstorGuard ca]
          refine ⟨postRegistry, imgPrev, hwfPost, hrPost, htargetPrev,
            hnewPrev, hpreviousPrev, hcontinuationPrev, hpostStor, ?_,
            hcodeToMid.trans (hcodeNewCount.trans hcodePostRegistry),
            hfinishRun⟩
          rw [hpostStor]
          exact hw.applySetPauserSourceTrace
            htargetCanonical hnewCanonical htrace

/-- The common event suffix preserves Registry storage and selects exactly one
caller continuation from the saved continuation word. -/
theorem finishSetPauser_run_split_continuation
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {newPauser previousPauser target continuation : B256}
    {ca : Adr}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (howner : sevm.currentTarget = ca)
    (hregisterLookup : fs[registerAfterSetSlot]? = some registerAfterSet)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hrun : Func.Run fs sevm pre finishSetPauser final) :
    (continuation = 0 ∧
      ∃ registerPre,
        pre.stack <<+ registerPre.stack ∧
        Mem.Wf registerPre.memory ∧
        Mem.Reads registerPre.memory img ∧
        Devm.getStor registerPre sevm.currentTarget =
          Devm.getStor pre ca ∧
        Devm.getCode pre = Devm.getCode registerPre ∧
        Func.Run fs sevm registerPre registerAfterSet final) ∨
    (continuation ≠ 0 ∧
      ∃ pausePre,
        pre.stack <<+ pausePre.stack ∧
        Mem.Wf pausePre.memory ∧
        Mem.Reads pausePre.memory img ∧
        Devm.getStor pausePre sevm.currentTarget =
          Devm.getStor pre ca ∧
        Devm.getCode pre = Devm.getCode pausePre ∧
        Func.Run fs sevm pausePre pauseAfterSet final) := by
  simp only [finishSetPauser] at hrun
  rcases of_run_prepend (loadWord newPauserWord) _ hrun with
    ⟨sNew, hloadNew, h1⟩
  rcases of_run_prepend (loadWord previousPauserWord) _ h1 with
    ⟨sPrevious, hloadPrevious, h2⟩
  rcases of_run_prepend (loadWord targetWord) _ h2 with
    ⟨sTarget, hloadTarget, h3⟩
  rcases of_run_next h3 with ⟨sEvent, hpushEvent, h4⟩
  rcases of_run_prepend (logWith 3 0 0) _ h4 with
    ⟨sLog, hlog, h5⟩
  rcases of_run_prepend (loadWord continuationWord) _ h5 with
    ⟨sContinuation, hloadContinuation, h6⟩
  rcases of_run_next h6 with ⟨sFlag, hiszero, hbranch⟩
  have hp0 : pre.stack <<+ pre.stack := by
    simpa only [List.append_nil] using pref_append pre.stack []
  rcases prefix_of_loadWord_image
      hp0 hwf hr hnewRead hloadNew with
    ⟨hpNew, hwfNew, hrNew, hstorNew⟩
  rcases prefix_of_loadWord_image
      hpNew hwfNew hrNew hpreviousRead hloadPrevious with
    ⟨hpPrevious, hwfPrevious, hrPrevious, hstorPrevious⟩
  rcases prefix_of_loadWord_image
      hpPrevious hwfPrevious hrPrevious htargetRead hloadTarget with
    ⟨hpTarget, hwfTarget, hrTarget, hstorTarget⟩
  have hpushEventInv := of_run_pushB256 hpushEvent
  have hpEvent :
      pauserSetEvent :: target :: previousPauser :: newPauser :: pre.stack
        <<+ sEvent.stack :=
    prefix_of_push hpushEventInv hpTarget
  have hwfEvent : Mem.Wf sEvent.memory := by
    rw [← hpushEventInv.memory]
    exact hwfTarget
  have hrEvent : Mem.Reads sEvent.memory img := by
    rw [← hpushEventInv.memory]
    exact hrTarget
  have hlog' : Line.Run sevm sEvent
      [pushB256 (0 * 32), pushB256 (0 * 32),
        log ((3 : Fin 4).succ)] sLog := by
    simpa [logWith] using hlog
  rcases Line.of_run_cons hlog' with
    ⟨sSize, hpushSize, hlogRest1⟩
  rcases Line.of_run_cons hlogRest1 with
    ⟨sOffset, hpushOffset, hlogRest2⟩
  rcases Line.of_run_cons hlogRest2 with
    ⟨sLog', hlogInst, hnil⟩
  cases hnil
  have hpushSizeInv := of_run_pushB256 hpushSize
  have hpushOffsetInv := of_run_pushB256 hpushOffset
  have hpSize :
      (0 : B256) :: pauserSetEvent :: target :: previousPauser ::
        newPauser :: pre.stack <<+ sSize.stack :=
    prefix_of_push hpushSizeInv hpEvent
  have hpOffset :
      (0 : B256) :: (0 : B256) :: pauserSetEvent :: target ::
        previousPauser :: newPauser :: pre.stack <<+ sOffset.stack :=
    prefix_of_push hpushOffsetInv hpSize
  let loggedWords : Stack :=
    [0, 0, pauserSetEvent, target, previousPauser, newPauser]
  have hpLogged : loggedWords ++ pre.stack <<+ sOffset.stack := by
    simpa [loggedWords] using hpOffset
  rcases of_run_log hlogInst with ⟨zs, hzsLength, hpopLog⟩
  have hpZs : zs <<+ sOffset.stack := pref_of_split hpopLog
  have hloggedLength :
      loggedWords.length = ((3 : Fin 4).succ).val + 2 := by
    simp [loggedWords]
  have hpLoggedHead : loggedWords <<+ sOffset.stack :=
    @pref_trans _ loggedWords (loggedWords ++ pre.stack) _
      ⟨pre.stack, rfl⟩ hpLogged
  have hzs : loggedWords = zs :=
    List.pref_unique (hloggedLength.trans hzsLength.symm)
      hpLoggedHead hpZs
  subst zs
  have hpLog : pre.stack <<+ sLog.stack :=
    of_append_pref hpopLog hpLogged
  have hwfOffset : Mem.Wf sOffset.memory := by
    rw [← hpushOffsetInv.memory, ← hpushSizeInv.memory]
    exact hwfEvent
  have hrOffset : Mem.Reads sOffset.memory img := by
    rw [← hpushOffsetInv.memory, ← hpushSizeInv.memory]
    exact hrEvent
  rcases of_run_log_mem hlogInst with ⟨mi, sz, hmemLog⟩
  have hwfLog : Mem.Wf sLog.memory := by
    rw [hmemLog]
    exact hwfOffset.extend mi sz
  have hrLog : Mem.Reads sLog.memory img := by
    rw [hmemLog]
    exact hrOffset.extend mi sz
  have hstorEvent : Devm.getStor sTarget = Devm.getStor sEvent :=
    Ninst.Hinv.inv (f := Devm.getStor) hpushEvent
  have hstorLog : Devm.getStor sEvent = Devm.getStor sLog :=
    Line.of_inv Devm.getStor (by line_inv) hlog
  have hstorPreLog : Devm.getStor pre = Devm.getStor sLog :=
    hstorNew.trans (hstorPrevious.trans
      (hstorTarget.trans (hstorEvent.trans hstorLog)))
  rcases prefix_of_loadWord_image
      hpLog hwfLog hrLog hcontinuationRead hloadContinuation with
    ⟨hpContinuation, hwfContinuation, hrContinuation,
      hstorContinuation⟩
  have hpFlag :
      (continuation =? 0) :: pre.stack <<+ sFlag.stack :=
    prefix_of_iszero hiszero hpContinuation
  have hmemIszero : sContinuation.memory = sFlag.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hiszero
  have hwfFlag : Mem.Wf sFlag.memory := by
    rw [← hmemIszero]
    exact hwfContinuation
  have hrFlag : Mem.Reads sFlag.memory img := by
    rw [← hmemIszero]
    exact hrContinuation
  have hstorIszero : Devm.getStor sContinuation = Devm.getStor sFlag :=
    Ninst.Hinv.inv (f := Devm.getStor) hiszero
  have hstorPreFlag : Devm.getStor pre = Devm.getStor sFlag :=
    hstorPreLog.trans (hstorContinuation.trans hstorIszero)
  have hcodePreFlag : Devm.getCode pre = Devm.getCode sFlag :=
    (Line.of_inv Devm.getCode (by line_inv) hloadNew).trans
      ((Line.of_inv Devm.getCode (by line_inv) hloadPrevious).trans
        ((Line.of_inv Devm.getCode (by line_inv) hloadTarget).trans
          ((Ninst.Hinv.inv (f := Devm.getCode) hpushEvent).trans
            ((Line.of_inv Devm.getCode (by line_inv) hlog).trans
              ((Line.of_inv Devm.getCode (by line_inv) hloadContinuation).trans
                (Ninst.Hinv.inv (f := Devm.getCode) hiszero))))))
  cases hbranch with
  | zero hpop hpauseCall =>
      rename_i pauseCallPre
      have hflag := (popBurn_pref hpop hpFlag).1
      have htail := (popBurn_pref hpop hpFlag).2
      have hcontinuation : continuation ≠ 0 := by
        intro heq
        rw [heq] at hflag
        simp [B256.eqCheck] at hflag
        exact (by decide : (0 : B256) ≠ 1) hflag
      rcases of_run_call hpauseCall with
        ⟨body, pausePre, hget, hburn, hbody⟩
      rw [hpauseLookup] at hget
      have hbodyEq : pauseAfterSet = body := Option.some.inj hget
      rw [← hbodyEq] at hbody
      have hstackBody : pre.stack <<+ pausePre.stack := by
        rw [← hburn.stack]
        exact htail
      have hmemBody : sFlag.memory = pausePre.memory :=
        hpop.memory.trans hburn.memory
      have hwfBody : Mem.Wf pausePre.memory := by
        rw [← hmemBody]
        exact hwfFlag
      have hrBody : Mem.Reads pausePre.memory img := by
        rw [← hmemBody]
        exact hrFlag
      have hstorBody : Devm.getStor pre = Devm.getStor pausePre :=
        hstorPreFlag.trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn))
      have hcodeBody : Devm.getCode pre = Devm.getCode pausePre :=
        hcodePreFlag.trans
          ((getCode_of_state_eq hpop.state).trans
            (getCode_of_state_eq hburn.state))
      right
      exact ⟨hcontinuation, pausePre, hstackBody, hwfBody, hrBody,
        by
          rw [howner]
          exact (congrFun hstorBody ca).symm,
        hcodeBody, hbody⟩
  | succ hnz hpop hbranchBurn hregisterCall =>
      rename_i flag afterPop registerCallPre
      have hflag : (continuation =? 0) = flag :=
        (List.of_cons_pref_of_cons_pref hpFlag
          (pref_of_split hpop.stack)).left
      have hcontinuation : continuation = 0 := by
        by_contra hne
        rw [B256.eqCheck, if_neg hne] at hflag
        exact hnz hflag.symm
      have htail : pre.stack <<+ afterPop.stack := by
        have hpFlag' : flag :: pre.stack <<+ sFlag.stack := by
          rwa [← hflag]
        exact (popBurn_pref hpop hpFlag').2
      have htailCall : pre.stack <<+ registerCallPre.stack := by
        rw [← hbranchBurn.stack]
        exact htail
      rcases of_run_call hregisterCall with
        ⟨body, registerPre, hget, hburn, hbody⟩
      rw [hregisterLookup] at hget
      have hbodyEq : registerAfterSet = body := Option.some.inj hget
      rw [← hbodyEq] at hbody
      have hstackBody : pre.stack <<+ registerPre.stack := by
        rw [← hburn.stack]
        exact htailCall
      have hmemBody : sFlag.memory = registerPre.memory :=
        hpop.memory.trans (hbranchBurn.memory.trans hburn.memory)
      have hwfBody : Mem.Wf registerPre.memory := by
        rw [← hmemBody]
        exact hwfFlag
      have hrBody : Mem.Reads registerPre.memory img := by
        rw [← hmemBody]
        exact hrFlag
      have hstorBody : Devm.getStor pre = Devm.getStor registerPre :=
        hstorPreFlag.trans
          ((PopBurn.Inv.inv hpop).trans
            ((Burn.Inv.inv hbranchBurn).trans (Burn.Inv.inv hburn)))
      have hcodeBody : Devm.getCode pre = Devm.getCode registerPre :=
        hcodePreFlag.trans
          ((getCode_of_state_eq hpop.state).trans
            ((getCode_of_state_eq hbranchBurn.state).trans
              (getCode_of_state_eq hburn.state)))
      left
      exact ⟨hcontinuation, registerPre, hstackBody, hwfBody, hrBody,
        by
          rw [howner]
          exact (congrFun hstorBody ca).symm,
        hcodeBody, hbody⟩

private theorem revertData_not_run
    {fs : List Func} {sevm : Sevm} {pre final : Devm} {blob : Bytes} :
    ¬ Func.Run fs sevm pre (Func.revertData blob) final := by
  have no_last : ∀ {s r : Devm},
      ¬ Func.Run fs sevm s (.last .revert) r := by
    intro s r run
    cases run with
    | last hrun =>
      simp only [Linst.Run, Linst.run] at hrun
      rcases Except.bind_eq_ok hrun with ⟨v1, h1, h2⟩
      rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
      rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
      contradiction
  have no_stores :
      ∀ (iws : List (B256 × Nat)) (rest : Func),
        (∀ {s r : Devm}, ¬ Func.Run fs sevm s rest r) →
        ∀ {s r : Devm},
          ¬ Func.Run fs sevm s (prependStoresRev iws rest) r := by
    intro iws
    induction iws with
    | nil =>
      intro rest h s r run
      exact h run
    | cons iw iws ih =>
      intro rest h
      simp only [prependStoresRev]
      apply ih
      intro s r run
      unfold prependStore at run
      rcases of_run_next run with ⟨s1, h1, run1⟩
      rcases of_run_next run1 with ⟨s2, h2, run2⟩
      rcases of_run_next run2 with ⟨s3, h3, run3⟩
      exact h run3
  unfold Func.revertData
  apply no_stores
  intro s r run
  rcases of_run_next run with ⟨s1, h1, run1⟩
  rcases of_run_next run1 with ⟨s2, h2, run2⟩
  exact no_last run2

private inductive Func.RunTo :
    List Func → Sevm → Devm → Func → Execution → Prop
  | zero {fs sevm pre afterPop f g out} :
      Devm.PopBurn [0] pre afterPop →
      Func.RunTo fs sevm afterPop f out →
      Func.RunTo fs sevm pre (Func.branch f g) out
  | succ {fs sevm pre w afterPop bodyPre f g out} :
      w ≠ 0 →
      Devm.PopBurn [w] pre afterPop →
      Devm.Burn afterPop bodyPre →
      Func.RunTo fs sevm bodyPre g out →
      Func.RunTo fs sevm pre (Func.branch f g) out
  | last {fs sevm pre l out} :
      Linst.Run sevm pre l out →
      Func.RunTo fs sevm pre (.last l) out
  | next {fs sevm pre i post f out} :
      Ninst.Run sevm pre i post →
      Func.RunTo fs sevm post f out →
      Func.RunTo fs sevm pre (.next i f) out
  | call {fs sevm pre bodyPre k f out} :
      fs[k]? = some f →
      Devm.Burn pre bodyPre →
      Func.RunTo fs sevm bodyPre f out →
      Func.RunTo fs sevm pre (.call k) out

private theorem Func.RunTo.of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {f : Func}
    (hrun : Func.Run fs sevm pre f post) :
    Func.RunTo fs sevm pre f (.ok post) := by
  induction hrun with
  | zero hpop _ ih => exact .zero hpop ih
  | succ hnz hpop hburn _ ih => exact .succ hnz hpop hburn ih
  | last hterminal => exact .last hterminal
  | next hstep _ ih => exact .next hstep ih
  | call hget hburn _ ih => exact .call hget hburn ih

private theorem Func.RunTo.of_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm} {f : Func}
    {out : Execution} (hrun : Func.RunCompiledTo fs sevm pre f out) :
    Func.RunTo fs sevm pre f out := by
  induction hrun with
  | zero hroom hpop _ ih =>
      exact .zero (Devm.PopBurn.of_popBurnBy hpop) ih
  | succ hnz hroom hpop _ ih =>
      exact .succ hnz (Devm.PopBurn.of_popBurnBy hpop) .refl ih
  | last hterminal => exact .last hterminal
  | next hstep _ ih => exact .next (Ninst.Run.of_runCompiled hstep) ih
  | call hget hroom hburn _ ih =>
      exact .call hget (Devm.Burn.of_burnBy hburn) ih

private lemma of_runTo_next {fs sevm devm i f out}
    (h : Func.RunTo fs sevm devm (Func.next i f) out) :
    ∃ devm', Ninst.Run sevm devm i devm' ∧
      Func.RunTo fs sevm devm' f out := by
  cases h with
  | next h1 h2 => exact ⟨_, h1, h2⟩

private lemma of_runTo_prepend {c e s out} :
    ∀ p q, Func.RunTo c e s (p +++ q) out →
      ∃ s', Line.Run e s p s' ∧ Func.RunTo c e s' q out
  | [], _, h => ⟨s, .nil, h⟩
  | (_ :: p), q, h => by
      rcases of_runTo_next h with ⟨s0, hi, htail⟩
      rcases of_runTo_prepend p q htail with ⟨s1, hp, hq⟩
      exact ⟨s1, .cons hi hp, hq⟩

private lemma of_runTo_call {fs : List Func} {sevm : Sevm}
    {s : Devm} {out : Execution} {k : Nat}
    (h : Func.RunTo fs sevm s (.call k) out) :
    ∃ f s', fs[k]? = some f ∧
      Devm.Burn s s' ∧ Func.RunTo fs sevm s' f out := by
  cases h with
  | call hget hburn hrun => exact ⟨_, _, hget, hburn, hrun⟩

/-- A source fragment whose successful prefix cannot touch persistent storage,
even when its terminal instruction returns an error outcome. -/
private inductive Func.StorSilent : Func → Prop
  | last {l : Linst} (h : l ≠ .selfdestruct) : StorSilent (.last l)
  | next {i : Ninst} {f : Func} [Ninst.Hinv Devm.getStor i]
      (hf : StorSilent f) : StorSilent (.next i f)

private theorem Func.StorSilent.effect
    {fs : List Func} {sevm : Sevm} {pre : Devm} {f : Func}
    {out : Execution} (hf : Func.StorSilent f)
    (hrun : Func.RunTo fs sevm pre f out) :
    Execution.Rel
      (fun before after => Devm.getStor before = Devm.getStor after)
      pre out := by
  induction hf generalizing pre with
  | last hne =>
      cases hrun with
      | last terminalRun =>
          have hi := Linst.run_instructionFrame sevm pre _ hne
          rw [terminalRun] at hi
          cases out <;> exact funext hi.getStor
  | @next i f _ _ ih =>
      cases hrun with
      | next instructionRun tail =>
          cases out <;>
            exact (Ninst.Hinv.inv (f := Devm.getStor) instructionRun).trans
              (ih tail)

private theorem prependStoresRev_storSilent
    (iws : List (B256 × Nat)) {rest : Func}
    (hrest : Func.StorSilent rest) :
    Func.StorSilent (prependStoresRev iws rest) := by
  induction iws generalizing rest with
  | nil => exact hrest
  | cons iw iws ih =>
      simp only [prependStoresRev]
      exact ih (.next (.next (.next hrest)))

private theorem revertData_storSilent (blob : Bytes) :
    Func.StorSilent (Func.revertData blob) := by
  unfold Func.revertData
  apply prependStoresRev_storSilent
  exact .next (.next (.last (by decide)))

private theorem RegistryWitness.of_storSilent_outcome
    {pre start : Devm} {out : Execution} {ca : Adr}
    {entries : List Entry}
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor start ca)) entries)
    (hstor : Execution.Rel
      (fun before after => Devm.getStor before = Devm.getStor after)
      start out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      pre out := by
  cases out with
  | error err =>
      change RegistryWitness
        (logicalStorageOfStor (Devm.getStor err.2 ca)) entries
      change Devm.getStor start = Devm.getStor err.2 at hstor
      rw [← congrFun hstor ca]
      exact hw
  | ok post =>
      change RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries
      change Devm.getStor start = Devm.getStor post at hstor
      rw [← congrFun hstor ca]
      exact hw

private theorem expiry_write_suffix
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {img : Bytes} {entries : List Entry} {pauser : B256}
    {ca : Adr} {xs : Stack} {word writeValue : B256} {tail : Func}
    (hstack : writeValue :: xs <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hread : Bytes.toB256
      (img.sliceD (word * 32).toNat 32 0) = pauser)
    (howner : sevm.currentTarget = ca)
    (hpauser : canonicalAddress pauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hrun : Func.RunTo fs sevm pre
      ((loadWord word ++ tagTop expiryRegion) +++ (sstore ::: tail)) out) :
    ∃ postStore,
      xs <<+ postStore.stack ∧
      Mem.Wf postStore.memory ∧
      Mem.Reads postStore.memory img ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor postStore ca)) entries ∧
      Func.RunTo fs sevm postStore tail out := by
  rcases of_runTo_prepend (loadWord word) _ hrun with
    ⟨sLoad, hload, h1⟩
  rcases of_runTo_prepend (tagTop expiryRegion) _ h1 with
    ⟨sKey, htag, h2⟩
  rcases of_runTo_next h2 with ⟨postStore, hstore, htail⟩
  rcases prefix_of_loadWord_image hstack hwf hr hread hload with
    ⟨hpLoad, hwfLoad, hrLoad, hsLoad⟩
  rcases prefix_of_tagTop hpLoad htag with ⟨hpKey, hmKey, hsKey⟩
  have hpStore : expirySlot pauser :: writeValue :: xs <<+ sKey.stack := by
    simpa [expirySlot] using hpKey
  have hmemStore : sKey.memory = postStore.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hstore
  have hwfStore : Mem.Wf postStore.memory := by
    rw [← hmemStore, ← hmKey]
    exact hwfLoad
  have hrStore : Mem.Reads postStore.memory img := by
    rw [← hmemStore, ← hmKey]
    exact hrLoad
  have hstackStore : xs <<+ postStore.stack :=
    prefix_of_sstore hstore hpStore
  have hstorBefore : Devm.getStor pre = Devm.getStor sKey :=
    hsLoad.trans hsKey
  rcases sstore_getStor_setStorVal hstore hpStore with ⟨value, hs⟩
  have hstorSet : Devm.getStor postStore ca =
      (Devm.getStor pre ca).set (expirySlot pauser)
        value := by
    rw [howner] at hs
    exact hs.trans (congrArg
      (fun stor => stor.set (expirySlot pauser) value)
      (congrFun hstorBefore ca).symm)
  have hwStore : RegistryWitness
      (logicalStorageOfStor (Devm.getStor postStore ca)) entries := by
    rw [hstorSet]
    exact hw.expiry_set hpauser
  exact ⟨postStore, hstackStore, hwfStore, hrStore, hwStore, htail⟩

private theorem register_write_body_preserves_registry
    {fs : List Func} {sevm : Sevm} {root pre : Devm} {out : Execution}
    {img : Bytes} {entries : List Entry} {newPauser : B256}
    {ca : Adr}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hrun : Func.RunTo fs sevm pre
      (dup 0 ::: mstoreAt 0 +++
        loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
        loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
        logWith 1 0 1 +++ Func.stop) out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      root out := by
  rcases of_runTo_next hrun with ⟨sDup, hdup, h1⟩
  rcases of_runTo_prepend (mstoreAt 0) _ h1 with
    ⟨sMem, hmstore, h2⟩
  rcases of_run_dup hdup with ⟨expiry, htop, _⟩
  cases hpreStack : pre.stack with
  | nil => simp [hpreStack] at htop
  | cons head tail =>
      simp [hpreStack] at htop
      subst head
      have hstack : expiry :: tail <<+ pre.stack := by
        simpa [hpreStack] using pref_append (expiry :: tail) []
      have hpDup : expiry :: expiry :: tail <<+ sDup.stack :=
        prefix_of_dup_val hdup (by show_nth) hstack
      have hmemDup : pre.memory = sDup.memory :=
        Ninst.Hinv.inv (f := Devm.memory) hdup
      have hstorDup : Devm.getStor pre = Devm.getStor sDup :=
        Ninst.Hinv.inv (f := Devm.getStor) hdup
      rcases of_run_mstoreAt_image hpDup (hmemDup ▸ hwf)
          (hmemDup ▸ hr) hmstore with
        ⟨hpMem, hwfMem, hrMem, hstorMem⟩
      let imgMem := Bytes.writeAt img 0 expiry.toBytes
      have hnewMem : Bytes.toB256
          (imgMem.sliceD (newPauserWord * 32).toNat 32 0) =
            newPauser := by
        dsimp [imgMem]
        rw [Bytes.sliceD_writeAt_after]
        · exact hnewRead
        · rw [B256.length_toBytes]
          decide
      have hwMem : RegistryWitness
          (logicalStorageOfStor (Devm.getStor sMem ca)) entries := by
        rw [← congrFun (hstorDup.trans hstorMem) ca]
        exact hw
      rcases expiry_write_suffix hpMem hwfMem hrMem hnewMem
          howner hnew hwMem h2 with
        ⟨postStore, _, _, _, hwStore, htail⟩
      have hsilent : Func.StorSilent
          (loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop) := by
        repeat' apply Func.StorSilent.next
        exact .last (by decide)
      exact hwStore.of_storSilent_outcome (hsilent.effect htail)

private theorem checkedHeartbeatExpiry_preserves_registry
    {fs : List Func} {sevm : Sevm} {root pre : Devm} {out : Execution}
    {img : Bytes} {entries : List Entry} {newPauser : B256}
    {ca : Adr} {panicData : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hpanicLookup : fs[arithmeticPanicSlot]? =
      some (Func.revertData panicData))
    (hrun : Func.RunTo fs sevm pre
      (checkedHeartbeatExpiry <|
        dup 0 ::: mstoreAt 0 +++
        loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
        loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
        logWith 1 0 1 +++ Func.stop) out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      root out := by
  simp only [checkedHeartbeatExpiry] at hrun
  let checkedLine : Line :=
    [timestamp, pushB256 heartbeatIntervalSlot, sload, add,
      dup 0, timestamp, swap 0, lt]
  have hshape :
      (timestamp ::: pushB256 heartbeatIntervalSlot ::: sload ::: add :::
        dup 0 ::: timestamp ::: swap 0 ::: lt :::
        ((.call arithmeticPanicSlot) <?>
          (dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop))) =
      checkedLine +++
        ((.call arithmeticPanicSlot) <?>
          (dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop)) := rfl
  rw [hshape] at hrun
  rcases of_runTo_prepend checkedLine _ hrun with
    ⟨sFlag, hprefix, hbranch⟩
  letI : Rinst.Hinv Devm.memory Rinst.timestamp := by
    show_hinv_mem_push
  have hmemPrefix : pre.memory = sFlag.memory :=
    Line.of_inv Devm.memory (by dsimp [checkedLine]; line_inv) hprefix
  have hstorPrefix : Devm.getStor pre = Devm.getStor sFlag :=
    Line.of_inv Devm.getStor (by dsimp [checkedLine]; line_inv) hprefix
  cases hbranch with
  | zero hpop hbody =>
      rename_i bodyPre
      have hmemBody : pre.memory = bodyPre.memory :=
        hmemPrefix.trans hpop.memory
      have hstorBody : Devm.getStor pre = Devm.getStor bodyPre :=
        hstorPrefix.trans (PopBurn.Inv.inv hpop)
      apply register_write_body_preserves_registry
        (hwf := hmemBody ▸ hwf) (hr := hmemBody ▸ hr)
        hnewRead howner hnew
      · rw [← congrFun hstorBody ca]
        exact hw
      · exact hbody
  | succ hnz hpop hbranchBurn hpanic =>
      rcases of_runTo_call hpanic with
        ⟨body, panicPre, hget, hburn, hbody⟩
      rw [hpanicLookup] at hget
      injection hget with heq
      subst body
      have hstorPanic : Devm.getStor pre = Devm.getStor panicPre :=
        hstorPrefix.trans
          ((PopBurn.Inv.inv hpop).trans
            ((Burn.Inv.inv hbranchBurn).trans (Burn.Inv.inv hburn)))
      have hwPanic : RegistryWitness
          (logicalStorageOfStor (Devm.getStor panicPre ca)) entries := by
        rw [← congrFun hstorPanic ca]
        exact hw
      exact hwPanic.of_storSilent_outcome
        ((revertData_storSilent panicData).effect hbody)

private theorem optional_new_preserves_registry
    {fs : List Func} {sevm : Sevm} {root pre : Devm} {out : Execution}
    {img : Bytes} {entries : List Entry} {newPauser : B256}
    {ca : Adr} {panicData : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hpanicLookup : fs[arithmeticPanicSlot]? =
      some (Func.revertData panicData))
    (hrun : Func.RunTo fs sevm pre
      (loadWord newPauserWord +++ iszero :::
        (Func.stop <?>
          (checkedHeartbeatExpiry <|
            dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop))) out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      root out := by
  rcases of_runTo_prepend (loadWord newPauserWord) _ hrun with
    ⟨sLoad, hload, h1⟩
  rcases of_runTo_next h1 with ⟨sFlag, hiszero, hbranch⟩
  have hp0 : pre.stack <<+ pre.stack := by
    simpa only [List.append_nil] using pref_append pre.stack []
  rcases prefix_of_loadWord_image hp0 hwf hr hnewRead hload with
    ⟨hpNew, hwfLoad, hrLoad, hstorLoad⟩
  have hmemIszero : sLoad.memory = sFlag.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hiszero
  have hstorIszero : Devm.getStor sLoad = Devm.getStor sFlag :=
    Ninst.Hinv.inv (f := Devm.getStor) hiszero
  have hwfFlag : Mem.Wf sFlag.memory := by
    rw [← hmemIszero]
    exact hwfLoad
  have hrFlag : Mem.Reads sFlag.memory img := by
    rw [← hmemIszero]
    exact hrLoad
  have hstorPrefix : Devm.getStor pre = Devm.getStor sFlag :=
    hstorLoad.trans hstorIszero
  cases hbranch with
  | zero hpop hbody =>
      rename_i bodyPre
      have hstorBody : Devm.getStor pre = Devm.getStor bodyPre :=
        hstorPrefix.trans (PopBurn.Inv.inv hpop)
      apply checkedHeartbeatExpiry_preserves_registry
        (hwf := by rw [← hpop.memory]; exact hwfFlag)
        (hr := by rw [← hpop.memory]; exact hrFlag)
        hnewRead howner hnew
      · rw [← congrFun hstorBody ca]
        exact hw
      · exact hpanicLookup
      · exact hbody
  | succ hnz hpop hburn hstop =>
      rename_i w afterPop stopPre
      have hstorAll : Devm.getStor pre = Devm.getStor stopPre :=
        hstorPrefix.trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn))
      have hwStop : RegistryWitness
          (logicalStorageOfStor (Devm.getStor stopPre ca)) entries := by
        rw [← congrFun hstorAll ca]
        exact hw
      exact hwStop.of_storSilent_outcome
        ((Func.StorSilent.last (by decide)).effect hstop)

private theorem clear_old_then_new_preserves_registry
    {fs : List Func} {sevm : Sevm} {root pre : Devm} {out : Execution}
    {img : Bytes} {entries : List Entry}
    {previousPauser newPauser : B256}
    {ca : Adr} {panicData : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hprevious : canonicalAddress previousPauser)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hpanicLookup : fs[arithmeticPanicSlot]? =
      some (Func.revertData panicData))
    (hrun : Func.RunTo fs sevm pre
      (pushB256 0 ::: loadWord previousPauserWord +++ tagTop expiryRegion +++
        sstore ::: pushB256 0 ::: mstoreAt 0 +++
        loadWord previousPauserWord +++ pushB256 heartbeatUpdatedEvent :::
        logWith 1 0 1 +++
        loadWord newPauserWord +++ iszero :::
        (Func.stop <?>
          (checkedHeartbeatExpiry <|
            dup 0 ::: mstoreAt 0 +++
            loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
            loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
            logWith 1 0 1 +++ Func.stop))) out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      root out := by
  rcases of_runTo_next hrun with ⟨sZero, hzero, h1⟩
  have hpPre : pre.stack <<+ pre.stack := by
    simpa only [List.append_nil] using pref_append pre.stack []
  have hpZero : (0 : B256) :: pre.stack <<+ sZero.stack :=
    prefix_of_push (of_run_pushB256 hzero) hpPre
  have hmemZero : pre.memory = sZero.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hzero
  have hstorZero : Devm.getStor pre = Devm.getStor sZero :=
    Ninst.Hinv.inv (f := Devm.getStor) hzero
  have hwZero : RegistryWitness
      (logicalStorageOfStor (Devm.getStor sZero ca)) entries := by
    rw [← congrFun hstorZero ca]
    exact hw
  rcases expiry_write_suffix hpZero
      (hmemZero ▸ hwf) (hmemZero ▸ hr) hpreviousRead
      howner hprevious hwZero h1 with
    ⟨postClear, hpClear, hwfClear, hrClear, hwClear, h2⟩
  rcases of_runTo_next h2 with ⟨sZero2, hzero2, h3⟩
  rcases of_runTo_prepend (mstoreAt 0) _ h3 with
    ⟨sMem, hmstore, h4⟩
  have hpZero2 : (0 : B256) :: pre.stack <<+ sZero2.stack :=
    prefix_of_push (of_run_pushB256 hzero2) hpClear
  have hmemZero2 : postClear.memory = sZero2.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hzero2
  have hstorZero2 : Devm.getStor postClear = Devm.getStor sZero2 :=
    Ninst.Hinv.inv (f := Devm.getStor) hzero2
  rcases of_run_mstoreAt_image hpZero2
      (hmemZero2 ▸ hwfClear) (hmemZero2 ▸ hrClear) hmstore with
    ⟨hpMem, hwfMem, hrMem, hstorMem⟩
  let imgMem := Bytes.writeAt img 0 (0 : B256).toBytes
  have hnewMem : Bytes.toB256
      (imgMem.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    dsimp [imgMem]
    rw [Bytes.sliceD_writeAt_after]
    · exact hnewRead
    · rw [B256.length_toBytes]
      decide
  have hpreviousMem : Bytes.toB256
      (imgMem.sliceD (previousPauserWord * 32).toNat 32 0) =
        previousPauser := by
    dsimp [imgMem]
    rw [Bytes.sliceD_writeAt_after]
    · exact hpreviousRead
    · rw [B256.length_toBytes]
      decide
  rcases of_runTo_prepend (loadWord previousPauserWord) _ h4 with
    ⟨sPrevious, hloadPrevious, h5⟩
  rcases of_runTo_next h5 with ⟨sEvent, hpushEvent, h6⟩
  rcases of_runTo_prepend (logWith 1 0 1) _ h6 with
    ⟨optionalPre, hlog, hoptional⟩
  rcases prefix_of_loadWord_image hpMem hwfMem hrMem hpreviousMem
      hloadPrevious with
    ⟨hpPrevious, hwfPrevious, hrPrevious, hstorPrevious⟩
  have hpushEventInv := of_run_pushB256 hpushEvent
  have hwfEvent : Mem.Wf sEvent.memory := by
    rw [← hpushEventInv.memory]
    exact hwfPrevious
  have hrEvent : Mem.Reads sEvent.memory imgMem := by
    rw [← hpushEventInv.memory]
    exact hrPrevious
  have hlog' : Line.Run sevm sEvent
      [pushB256 (1 * 32), pushB256 (0 * 32),
        log ((1 : Fin 4).succ)] optionalPre := by
    simpa [logWith] using hlog
  rcases Line.of_run_cons hlog' with
    ⟨sSize, hpushSize, hlogRest1⟩
  rcases Line.of_run_cons hlogRest1 with
    ⟨sOffset, hpushOffset, hlogRest2⟩
  rcases Line.of_run_cons hlogRest2 with
    ⟨sLog, hlogInst, hnil⟩
  cases hnil
  have hpushSizeInv := of_run_pushB256 hpushSize
  have hpushOffsetInv := of_run_pushB256 hpushOffset
  have hwfOffset : Mem.Wf sOffset.memory := by
    rw [← hpushOffsetInv.memory, ← hpushSizeInv.memory]
    exact hwfEvent
  have hrOffset : Mem.Reads sOffset.memory imgMem := by
    rw [← hpushOffsetInv.memory, ← hpushSizeInv.memory]
    exact hrEvent
  rcases of_run_log_mem hlogInst with ⟨mi, sz, hmemLog⟩
  have hwfOptional : Mem.Wf optionalPre.memory := by
    rw [hmemLog]
    exact hwfOffset.extend mi sz
  have hrOptional : Mem.Reads optionalPre.memory imgMem := by
    rw [hmemLog]
    exact hrOffset.extend mi sz
  have hstorEvent : Devm.getStor sMem = Devm.getStor optionalPre :=
    hstorPrevious.trans
      ((Ninst.Hinv.inv (f := Devm.getStor) hpushEvent).trans
        (Line.of_inv Devm.getStor (by line_inv) hlog))
  have hwOptional : RegistryWitness
      (logicalStorageOfStor (Devm.getStor optionalPre ca)) entries := by
    rw [← congrFun hstorEvent ca, ← congrFun hstorMem ca,
      ← congrFun hstorZero2 ca]
    exact hwClear
  exact optional_new_preserves_registry hwfOptional hrOptional hnewMem
    howner hnew hwOptional hpanicLookup hoptional

private theorem previous_count_branch_preserves_registry
    {fs : List Func} {sevm : Sevm} {root pre : Devm} {out : Execution}
    {img : Bytes} {entries : List Entry}
    {previousPauser newPauser : B256}
    {ca : Adr} {panicData : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hprevious : canonicalAddress previousPauser)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hpanicLookup : fs[arithmeticPanicSlot]? =
      some (Func.revertData panicData))
    (hrun : Func.RunTo fs sevm pre
      (previousCountKey +++ sload ::: iszero :::
        (pushB256 0 ::: loadWord previousPauserWord +++
          tagTop expiryRegion +++ sstore ::: pushB256 0 ::: mstoreAt 0 +++
          loadWord previousPauserWord +++
          pushB256 heartbeatUpdatedEvent ::: logWith 1 0 1 +++
          loadWord newPauserWord +++ iszero :::
          (Func.stop <?>
            (checkedHeartbeatExpiry <|
              dup 0 ::: mstoreAt 0 +++
              loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
              loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
              logWith 1 0 1 +++ Func.stop))) <?>
        (loadWord newPauserWord +++ iszero :::
          (Func.stop <?>
            (checkedHeartbeatExpiry <|
              dup 0 ::: mstoreAt 0 +++
              loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
              loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
              logWith 1 0 1 +++ Func.stop)))) out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      root out := by
  rcases of_runTo_prepend previousCountKey _ hrun with
    ⟨sKey, hkey, h1⟩
  rcases of_runTo_next h1 with ⟨sLoad, hsload, h2⟩
  rcases of_runTo_next h2 with ⟨sFlag, hiszero, hbranch⟩
  have hp0 : pre.stack <<+ pre.stack := by
    simpa only [List.append_nil] using pref_append pre.stack []
  rcases prefix_of_previousCountKey_image hp0 hwf hr hpreviousRead hkey with
    ⟨hpKey, hwfKey, hrKey, hstorKey⟩
  rcases prefix_of_sload hsload hpKey with
    ⟨count, hpCount, _⟩
  have hpFlag : (count =? 0) :: pre.stack <<+ sFlag.stack :=
    prefix_of_iszero hiszero hpCount
  have hmemArith : sKey.memory = sFlag.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hsload (Line.Run.cons hiszero Line.Run.nil))
  have hstorArith : Devm.getStor sKey = Devm.getStor sFlag :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons hsload (Line.Run.cons hiszero Line.Run.nil))
  have hwfFlag : Mem.Wf sFlag.memory := by
    rw [← hmemArith]
    exact hwfKey
  have hrFlag : Mem.Reads sFlag.memory img := by
    rw [← hmemArith]
    exact hrKey
  have hstorPrefix : Devm.getStor pre = Devm.getStor sFlag :=
    hstorKey.trans hstorArith
  cases hbranch with
  | zero hpop hoptional =>
      rename_i optionalPre
      have hwOptional : RegistryWitness
          (logicalStorageOfStor (Devm.getStor optionalPre ca)) entries := by
        rw [← congrFun (hstorPrefix.trans (PopBurn.Inv.inv hpop)) ca]
        exact hw
      exact optional_new_preserves_registry
        (by rw [← hpop.memory]; exact hwfFlag)
        (by rw [← hpop.memory]; exact hrFlag)
        hnewRead howner hnew hwOptional hpanicLookup hoptional
  | succ hnz hpop hburn hclear =>
      rename_i w afterPop clearPre
      have hmemClear : sFlag.memory = clearPre.memory :=
        hpop.memory.trans hburn.memory
      have hstorClear : Devm.getStor pre = Devm.getStor clearPre :=
        hstorPrefix.trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn))
      have hwClear : RegistryWitness
          (logicalStorageOfStor (Devm.getStor clearPre ca)) entries := by
        rw [← congrFun hstorClear ca]
        exact hw
      exact clear_old_then_new_preserves_registry
        (by rw [← hmemClear]; exact hwfFlag)
        (by rw [← hmemClear]; exact hrFlag)
        hpreviousRead hnewRead howner hprevious hnew hwClear
        hpanicLookup hclear

private theorem registerAfterSet_runTo_preserves_registry
    {fs : List Func} {sevm : Sevm} {root pre : Devm} {out : Execution}
    {img : Bytes} {entries : List Entry}
    {previousPauser newPauser : B256}
    {ca : Adr} {panicData : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hprevious : canonicalAddress previousPauser)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hpanicLookup : fs[arithmeticPanicSlot]? =
      some (Func.revertData panicData))
    (hrun : Func.RunTo fs sevm pre registerAfterSet out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      root out := by
  simp only [registerAfterSet] at hrun
  rcases of_runTo_prepend (loadWord previousPauserWord) _ hrun with
    ⟨sPrevious, hloadPrevious, h1⟩
  rcases of_runTo_next h1 with ⟨sFlag, hiszero, hbranch⟩
  have hp0 : pre.stack <<+ pre.stack := by
    simpa only [List.append_nil] using pref_append pre.stack []
  rcases prefix_of_loadWord_image hp0 hwf hr hpreviousRead
      hloadPrevious with
    ⟨hpPrevious, hwfPrevious, hrPrevious, hstorPrevious⟩
  have hpFlag : (previousPauser =? 0) :: pre.stack <<+ sFlag.stack :=
    prefix_of_iszero hiszero hpPrevious
  have hmemIszero : sPrevious.memory = sFlag.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hiszero
  have hstorIszero : Devm.getStor sPrevious = Devm.getStor sFlag :=
    Ninst.Hinv.inv (f := Devm.getStor) hiszero
  have hwfFlag : Mem.Wf sFlag.memory := by
    rw [← hmemIszero]
    exact hwfPrevious
  have hrFlag : Mem.Reads sFlag.memory img := by
    rw [← hmemIszero]
    exact hrPrevious
  have hstorPrefix : Devm.getStor pre = Devm.getStor sFlag :=
    hstorPrevious.trans hstorIszero
  cases hbranch with
  | zero hpop hpreviousBranch =>
      rename_i previousPre
      have hwPrevious : RegistryWitness
          (logicalStorageOfStor (Devm.getStor previousPre ca)) entries := by
        rw [← congrFun (hstorPrefix.trans (PopBurn.Inv.inv hpop)) ca]
        exact hw
      exact previous_count_branch_preserves_registry (root := root)
        (by rw [← hpop.memory]; exact hwfFlag)
        (by rw [← hpop.memory]; exact hrFlag)
        hpreviousRead hnewRead howner hprevious hnew hwPrevious
        hpanicLookup hpreviousBranch
  | succ hnz hpop hburn hoptional =>
      rename_i w afterPop optionalPre
      have hmemOptional : sFlag.memory = optionalPre.memory :=
        hpop.memory.trans hburn.memory
      have hstorOptional : Devm.getStor pre = Devm.getStor optionalPre :=
        hstorPrefix.trans
          ((PopBurn.Inv.inv hpop).trans (Burn.Inv.inv hburn))
      have hwOptional : RegistryWitness
          (logicalStorageOfStor (Devm.getStor optionalPre ca)) entries := by
        rw [← congrFun hstorOptional ca]
        exact hw
      exact optional_new_preserves_registry (root := root)
        (by rw [← hmemOptional]; exact hwfFlag)
        (by rw [← hmemOptional]; exact hrFlag)
        hnewRead howner hnew hwOptional hpanicLookup hoptional

/-- Every successful source `registerAfterSet` run preserves the Registry
witness.  Its zero/no-op paths execute no expiry write, its ordinary paths
execute one, and the last-assignment path may execute two (including twice at
the same expiry key).  A checked-expiry overflow cannot be a successful run. -/
theorem registerAfterSet_preserves_registry
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {entries : List Entry}
    {previousPauser newPauser : B256}
    {ca : Adr} {panicData : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hprevious : canonicalAddress previousPauser)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hpanicLookup : fs[arithmeticPanicSlot]? =
      some (Func.revertData panicData))
    (hrun : Func.Run fs sevm pre registerAfterSet final) :
    RegistryWitness
      (logicalStorageOfStor (Devm.getStor final ca)) entries := by
  exact registerAfterSet_runTo_preserves_registry
    (root := pre) hwf hr hpreviousRead hnewRead howner hprevious hnew hw
    hpanicLookup (Func.RunTo.of_run hrun)

/-- Every raw compiled source walk through `registerAfterSet` preserves the
Registry witness at its actual output state.  This includes the checked-expiry
panic/revert path and every zero-, one-, or two-expiry-write path; expiry slots
are disjoint from every Registry region, including when both writes use the
same expiry key. -/
theorem registerAfterSet_runCompiledTo_preserves_registry
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {img : Bytes} {entries : List Entry}
    {previousPauser newPauser : B256}
    {ca : Adr} {panicData : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hprevious : canonicalAddress previousPauser)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hpanicLookup : fs[arithmeticPanicSlot]? =
      some (Func.revertData panicData))
    (hrun : Func.RunCompiledTo fs sevm pre registerAfterSet out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      pre out := by
  exact registerAfterSet_runTo_preserves_registry
    (root := pre) hwf hr hpreviousRead hnewRead howner hprevious hnew hw
    hpanicLookup (Func.RunTo.of_runCompiledTo hrun)

/-- Canonical direct-call calldata for `registerPauser(address,address)`. -/
def registerPauserCalldata (target newPauser : B256) : Bytes :=
  abiSelectorBytes (selector "registerPauser" [.address, .address]) ++
    target.toBytes ++ newPauser.toBytes

/-- Canonical direct-call calldata for `pause(address)`. -/
def pauseCalldata (target : B256) : Bytes :=
  abiSelectorBytes (selector "pause" [.address]) ++ target.toBytes

/-- Message-frame settlement restores every entry-state Registry witness on an
error outcome, independently of where that error occurred in the raw frame. -/
theorem RegistryWitness.of_ProcessMessage_error
    {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr} {entries : List Entry}
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome)
    (hentry : RegistryWitness
      (logicalStorageOfStor (msg.benv.state.getStor ca)) entries) :
    RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries := by
  have hstate := (ProcessMessage.rollback_of_error hprocess herror).1
  have hstor : Devm.getStor post ca = msg.benv.state.getStor ca :=
    congrArg (fun state : State => state.getStor ca) hstate
  rw [hstor]
  exact hentry

/-- Every settled error of an exact direct production `registerPauser` message
restores the message-entry Registry at the concrete contract owner. -/
theorem registerPauser_settled_error_restores_registry
    (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr} {entries : List Entry} {target newPauser : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = registerPauserCalldata target newPauser)
    (_htargetCanonical : canonicalAddress target)
    (_hnewCanonical : canonicalAddress newPauser)
    (hentry : RegistryWitness
      (logicalStorageOfStor (msg.benv.state.getStor ca)) entries)
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome) :
    RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries :=
  hentry.of_ProcessMessage_error hprocess herror

/-- Every settled error of an exact direct production `pause` message restores
the message-entry Registry at the concrete contract owner. -/
theorem pause_settled_error_restores_registry
    (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr} {entries : List Entry} {target : B256}
    (_htarget : msg.target = some ca)
    (_howner : msg.currentTarget = ca)
    (_hcodeAddress : msg.codeAddress = some ca)
    (_hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (_hvalue : msg.value = 0)
    (_hdata : msg.data = pauseCalldata target)
    (_htargetCanonical : canonicalAddress target)
    (hentry : RegistryWitness
      (logicalStorageOfStor (msg.benv.state.getStor ca)) entries)
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome) :
    RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries :=
  hentry.of_ProcessMessage_error hprocess herror

/-! ## Private target-zero exact-execution certificate

These declarations are deliberately local to the Lido Registry proof.  They
certify only the forward-constructed `PausableZero` path and do not add a new
generic execution-occurrence framework. -/

/-- Structural raw-node freedom for the one exact execution tree constructed
by the target-zero theorem. -/
private inductive Exec.TargetZeroRawSstoreFree :
    {pc : Nat} → {sevm : Sevm} → {pre : Devm} → {out : Execution} →
      Exec pc sevm pre out → Prop
  | halt {pc sevm pre out}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .halt out}
      (root : ¬ Ninst.At sevm.code pc (.reg .sstore)) :
      Exec.TargetZeroRawSstoreFree (.halt step)
  | cont {pc pc' sevm pre post out}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post}
      {next : Exec pc' sevm post out}
      (root : ¬ Ninst.At sevm.code pc (.reg .sstore))
      (tail : Exec.TargetZeroRawSstoreFree next) :
      Exec.TargetZeroRawSstoreFree (.cont step next)
  | doneErr {pc pc' sevm pre frame resume settled error}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
      {enter : frame.enter = .done settled}
      {resumeError : resume.run settled = .error error}
      (root : ¬ Ninst.At sevm.code pc (.reg .sstore)) :
      Exec.TargetZeroRawSstoreFree (.doneErr step enter resumeError)
  | doneOk {pc pc' sevm pre post frame resume settled out}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
      {enter : frame.enter = .done settled}
      {resumeOk : resume.run settled = .ok post}
      {next : Exec pc' sevm post out}
      (root : ¬ Ninst.At sevm.code pc (.reg .sstore))
      (tail : Exec.TargetZeroRawSstoreFree next) :
      Exec.TargetZeroRawSstoreFree (.doneOk step enter resumeOk next)
  | runErr {pc pc' sevm pre frame resume childEvm raw error}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
      {enter : frame.enter = .run childEvm}
      {child : Exec childEvm.pc childEvm.sta childEvm.dyna raw}
      {resumeError : resume.run (frame.settle raw) = .error error}
      (root : ¬ Ninst.At sevm.code pc (.reg .sstore))
      (childFree : Exec.TargetZeroRawSstoreFree child) :
      Exec.TargetZeroRawSstoreFree (.runErr step enter child resumeError)
  | runOk {pc pc' sevm pre post frame resume childEvm raw out}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
      {enter : frame.enter = .run childEvm}
      {child : Exec childEvm.pc childEvm.sta childEvm.dyna raw}
      {resumeOk : resume.run (frame.settle raw) = .ok post}
      {next : Exec pc' sevm post out}
      (root : ¬ Ninst.At sevm.code pc (.reg .sstore))
      (childFree : Exec.TargetZeroRawSstoreFree child)
      (tail : Exec.TargetZeroRawSstoreFree next) :
      Exec.TargetZeroRawSstoreFree (.runOk step enter child resumeOk next)

private theorem Exec.TargetZeroRawSstoreFree.noSstoreAt
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (safe : Exec.TargetZeroRawSstoreFree run) :
    ∀ node : Exec.Deriv,
      node ∈ Exec.rawNodes run →
      Ninst.At node.sevm.code node.pc (.reg .sstore) → False := by
  induction safe with
  | halt root =>
      intro node reached storeAt
      simp only [Exec.rawNodes, List.mem_singleton] at reached
      subst node
      exact root storeAt
  | cont root tail ih =>
      intro node reached storeAt
      simp only [Exec.rawNodes, List.mem_cons] at reached
      rcases reached with rfl | reached
      · exact root storeAt
      · exact ih node reached storeAt
  | doneErr root =>
      intro node reached storeAt
      simp only [Exec.rawNodes, List.mem_singleton] at reached
      subst node
      exact root storeAt
  | doneOk root tail ih =>
      intro node reached storeAt
      simp only [Exec.rawNodes, List.mem_cons] at reached
      rcases reached with rfl | reached
      · exact root storeAt
      · exact ih node reached storeAt
  | runErr root childFree ih =>
      intro node reached storeAt
      simp only [Exec.rawNodes, List.mem_cons] at reached
      rcases reached with rfl | reached
      · exact root storeAt
      · exact ih node reached storeAt
  | runOk root childFree tail childIH tailIH =>
      intro node reached storeAt
      simp only [Exec.rawNodes, List.mem_cons, List.mem_append] at reached
      rcases reached with rfl | reached
      · exact root storeAt
      · rcases reached with reached | reached
        · exact childIH node reached storeAt
        · exact tailIH node reached storeAt

/-- Path certificate indexed by the actual forward `RunCompiledTo` proof.  A
`.next` node must be both non-SSTORE and childless; selected branches and
internal source calls recurse only into their executed body. -/
private inductive Func.RunCompiledTo.TargetZeroPathFree :
    ∀ {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
      {out : Execution}, Func.RunCompiledTo fs sevm pre body out → Prop
  | zero {fs : List Func} {sevm : Sevm} {pre post : Devm}
      {left right : Func} {out : Execution}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [0] (gVerylow + gHigh) pre post}
      {tail : Func.RunCompiledTo fs sevm post left out}
      (tailFree : Func.RunCompiledTo.TargetZeroPathFree tail) :
      Func.RunCompiledTo.TargetZeroPathFree
        (.zero (g := right) room pop tail)
  | succ {fs : List Func} {sevm : Sevm} {pre post : Devm}
      {word : B256} {left right : Func} {out : Execution}
      {nonzero : word ≠ 0}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [word]
        (gVerylow + gHigh + gJumpdest) pre post}
      {tail : Func.RunCompiledTo fs sevm post right out}
      (tailFree : Func.RunCompiledTo.TargetZeroPathFree tail) :
      Func.RunCompiledTo.TargetZeroPathFree
        (.succ (f := left) nonzero room pop tail)
  | last {fs : List Func} {sevm : Sevm} {pre : Devm}
      {terminal : Linst} {out : Execution}
      {terminalRun : Linst.Run sevm pre terminal out} :
      Func.RunCompiledTo.TargetZeroPathFree
        (Func.RunCompiledTo.last (fs := fs) terminalRun)
  | next {fs : List Func} {sevm : Sevm} {pre post : Devm}
      {instruction : Ninst} {body : Func} {out : Execution}
      {instructionRun : Ninst.RunCompiled sevm pre instruction post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (instructionNe : instruction ≠ .reg .sstore)
      (instructionChildless : ∀ operation : Xinst,
        instruction ≠ .exec operation)
      (tailFree : Func.RunCompiledTo.TargetZeroPathFree tail) :
      Func.RunCompiledTo.TargetZeroPathFree (.next instructionRun tail)
  | call {fs : List Func} {sevm : Sevm} {pre post : Devm}
      {index : Nat} {body : Func} {out : Execution}
      {lookup : fs[index]? = some body}
      {room : pre.stack.length < 1024}
      {burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (tailFree : Func.RunCompiledTo.TargetZeroPathFree tail) :
      Func.RunCompiledTo.TargetZeroPathFree (.call lookup room burn tail)

/-- Childless `.next` companion to the construction used by the compiler
bridge, retaining raw-node freedom. -/
private lemma Ninst.exists_exec_targetZeroRawSstoreFree
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    {instruction : Ninst} {out : Execution}
    (instructionAt : Ninst.At sevm.code pc instruction)
    (instructionRun : Ninst.RunCompiled sevm pre instruction post)
    (instructionNe : instruction ≠ .reg .sstore)
    (instructionChildless : ∀ operation : Xinst,
      instruction ≠ .exec operation)
    {tail : Exec (pc + instruction.size) sevm post out}
    (tailFree : Exec.TargetZeroRawSstoreFree tail) :
    ∃ run : Exec pc sevm pre out,
      Exec.TargetZeroRawSstoreFree run := by
  have rootFree : ¬ Ninst.At sevm.code pc (.reg .sstore) := by
    intro storeAt
    exact instructionNe (Ninst.at_unique instructionAt storeAt)
  have evmStep : Evm.step ⟨pc, sevm, pre⟩ =
      Ninst.step ⟨pc, sevm, pre⟩ instruction :=
    Evm.step_next instructionAt
  rcases instructionRun with ⟨slot, filled, steps⟩
  have stepRun := steps pc
  cases instruction with
  | reg operation =>
      rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
      have step : Evm.step ⟨pc, sevm, pre⟩ = .cont (pc + 1) post := by
        rw [evmStep, Ninst.step_reg, ← stepRun.2]
        rfl
      exact ⟨.cont step tail, .cont rootFree tailFree⟩
  | push bytes length =>
      rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at stepRun
      have step : Evm.step ⟨pc, sevm, pre⟩ =
          .cont (pc + Ninst.size (.push bytes length)) post := by
        rw [evmStep, Ninst.step_push, ← stepRun.2]
        rfl
      exact ⟨.cont step tail, .cont rootFree tailFree⟩
  | exec operation =>
      exact (instructionChildless operation rfl).elim

/-- Construction-direction compiler bridge specialized to the private
target-zero path certificate. -/
private theorem Func.RunCompiledTo.exists_exec_targetZeroRawSstoreFree :
    ∀ {f₀ : Func} {fs' : List Func} {sevm : Sevm} {fs : List Func}
      {pre : Devm} {body : Func} {out : Execution}
      (run : Func.RunCompiledTo fs sevm pre body out),
      Func.RunCompiledTo.TargetZeroPathFree run →
      some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩ →
      fs = f₀ :: fs' →
      ∀ pc,
        subcode sevm.code.toList pc
          (Func.compile (table 0 (f₀ :: fs')) pc body) →
        noPushBefore sevm.code pc 32 = true →
        ∃ execution : Exec pc sevm pre out,
          Exec.TargetZeroRawSstoreFree execution := by
  intro f₀ fs' sevm fs pre body out run safe
  induction safe with
  | @zero certPre certPost left right certOut
      room pop tail tailFree ih =>
      intro compiled tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpiAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_zero_steps pushAt jumpiAt locAt room pop with
        ⟨pushStep, jumpStep⟩
      rcases ih compiled tableEq (pc + 4) leftSub leftNoPush with
        ⟨leftRun, leftFree⟩
      have pushFree : ¬ Ninst.At sevm.code pc (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.at_unique pushAt storeAt
        cases impossible
      have jumpFree :
          ¬ Ninst.At sevm.code (pc + 3) (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpiAt
      exact ⟨.cont pushStep (.cont jumpStep leftRun),
        .cont pushFree (.cont jumpFree leftFree)⟩
  | @succ certPre certPost word left right certOut
      nonzero room pop tail tailFree ih =>
      intro compiled tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpiAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_succ_steps pushAt jumpiAt jumpdestAt jumpable
        locAt nonzero room pop with
        ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih compiled tableEq (loc + 1) rightSub rightNoPush with
        ⟨rightRun, rightFree⟩
      have pushFree : ¬ Ninst.At sevm.code pc (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.at_unique pushAt storeAt
        cases impossible
      have jumpFree :
          ¬ Ninst.At sevm.code (pc + 3) (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpiAt
      have jumpdestFree : ¬ Ninst.At sevm.code loc (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpdestAt
      exact ⟨.cont pushStep (.cont jumpStep
          (.cont jumpdestStep rightRun)),
        .cont pushFree (.cont jumpFree
          (.cont jumpdestFree rightFree))⟩
  | @last certPre terminal certOut terminalRun =>
      intro compiled tableEq pc sub noPush
      have terminalAt := Linst.at_of_slice sub
      have step : Evm.step ⟨pc, sevm, certPre⟩ = .halt certOut := by
        rw [Evm.step_last terminalAt]
        exact congrArg Step.halt terminalRun
      have terminalFree : ¬ Ninst.At sevm.code pc (.reg .sstore) :=
        fun storeAt => storeAt.false_of_linstAt terminalAt
      exact ⟨.halt step, .halt terminalFree⟩
  | @next certPre certPost instruction certBody certOut
      instructionRun tail instructionNe instructionChildless tailFree ih =>
      intro compiled tableEq pc sub noPush
      rcases Func.noPushBefore_next sub noPush with
        ⟨tailNoPush, tailSub⟩
      rcases of_subcode sub with ⟨code, compileEq, slice⟩
      rcases of_bind_eq_some compileEq with
        ⟨tailCode, tailCompileEq, codeEq⟩
      simp [pure] at codeEq
      rw [← codeEq] at slice
      have instructionAt : Ninst.At sevm.code pc _ :=
        Ninst.at_of_slice (List.slice_prefix slice)
      rcases ih compiled tableEq _ tailSub tailNoPush with
        ⟨tailRun, tailExecutionFree⟩
      exact Ninst.exists_exec_targetZeroRawSstoreFree instructionAt
        instructionRun instructionNe instructionChildless tailExecutionFree
  | @call certPre certPost index certBody certOut
      lookup room burn tail tailFree ih =>
      intro compiled tableEq pc sub noPush
      subst tableEq
      rcases subcode_compile_call sub with
        ⟨loc, compiledBody, tableLookup, locBound, pushAt, jumpAt⟩
      have selected := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) tableLookup)
      rw [lookup] at selected
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at selected
      subst selected
      rcases subcode_of_get?_eq_some compiled tableLookup with
        ⟨jumpdestAt, bodySub⟩
      have bodyJumpable := Prog.jumpable_of_get?_table compiled tableLookup
      rcases pushAt with ⟨length, pushAt⟩
      rcases Evm.call_steps (le := length) pushAt jumpAt jumpdestAt
        bodyJumpable.1 locBound room burn with
        ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih compiled rfl (loc + 1) bodySub bodyJumpable.2 with
        ⟨bodyRun, bodyFree⟩
      have pushFree : ¬ Ninst.At sevm.code pc (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.at_unique pushAt storeAt
        cases impossible
      have jumpFree :
          ¬ Ninst.At sevm.code (pc + 3) (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpAt
      have jumpdestFree : ¬ Ninst.At sevm.code loc (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpdestAt
      exact ⟨.cont pushStep (.cont jumpStep
          (.cont jumpdestStep bodyRun)),
        .cont pushFree (.cont jumpFree
          (.cont jumpdestFree bodyFree))⟩

/-! ## Private direct-pause post-write path certificate

This certificate is deliberately contract-local.  It remembers one exact
assignment-clear `SSTORE`, a later zero-code `EXTCODESIZE`, and that every
other selected source instruction is childless. -/

private inductive DirectPausePhase where
  | beforeWrite
  | beforeZeroCode
  | afterZeroCode

set_option linter.unusedVariables false in
private inductive Func.RunCompiledTo.DirectPausePath
    (ca : Adr) (target : B256) :
    ∀ {phase : DirectPausePhase} {fs : List Func} {sevm : Sevm}
      {pre : Devm} {body : Func} {out : Execution},
      Func.RunCompiledTo fs sevm pre body out → Prop
  | zero {fs sevm pre post left right out phase}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [0] (gVerylow + gHigh) pre post}
      {tail : Func.RunCompiledTo fs sevm post left out}
      (tailPath : Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) tail) :
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase)
        (.zero (g := right) room pop tail)
  | succ {fs sevm pre post left right out phase word}
      {nonzero : word ≠ 0}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [word]
        (gVerylow + gHigh + gJumpdest) pre post}
      {tail : Func.RunCompiledTo fs sevm post right out}
      (tailPath : Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) tail) :
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase)
        (.succ (f := left) nonzero room pop tail)
  | last {fs sevm pre terminal out}
      {terminalRun : Linst.Run sevm pre terminal out} :
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := .afterZeroCode)
        (Func.RunCompiledTo.last (fs := fs) terminalRun)
  | next {fs sevm pre post instruction body out phase}
      {instructionRun : Ninst.RunCompiled sevm pre instruction post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (childless : ∀ operation : Xinst, instruction ≠ .exec operation)
      (tailPath : Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) tail) :
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase)
        (.next instructionRun tail)
  | call {fs sevm pre post index body out phase}
      {lookup : fs[index]? = some body}
      {room : pre.stack.length < 1024}
      {burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (tailPath : Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) tail) :
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase)
        (.call lookup room burn tail)
  | zeroCode {fs sevm pre post body out}
      {instructionRun : Ninst.RunCompiled sevm pre
        (.reg .extcodesize) post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (stack : ∃ rest, pre.stack = target :: rest)
      (codeSize : (pre.getCode target.toAdr).size = 0)
      (tailPath : Func.RunCompiledTo.DirectPausePath ca target
        (phase := .afterZeroCode) tail) :
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := .beforeZeroCode) (.next instructionRun tail)
  | write {fs sevm pre post body out}
      {instructionRun : Ninst.RunCompiled sevm pre (.reg .sstore) post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (owner : sevm.currentTarget = ca)
      (popped : Stack.Pop [assignmentSlot target, 0]
        pre.stack post.stack)
      (tailPath : Func.RunCompiledTo.DirectPausePath ca target
        (phase := .beforeZeroCode) tail) :
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := .beforeWrite) (.next instructionRun tail)

/-- Prepend an ordinary (unmarked) storage write to a constructed direct-pause
path.  The write remains a childless `.next`, so it preserves its phase. -/
private theorem directPausePath_prepend_sstore
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {body : Func} {out : Execution}
    (instructionRun : Ninst.RunCompiled sevm pre (.reg .sstore) post)
    (tail : Func.RunCompiledTo fs sevm post body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca target
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (.reg .sstore ::: body) out,
      Func.RunCompiledTo.DirectPausePath ca target (phase := phase) run := by
  let run : Func.RunCompiledTo fs sevm pre (.reg .sstore ::: body) out :=
    .next instructionRun tail
  have path : Func.RunCompiledTo.DirectPausePath ca target
      (phase := phase) run :=
    .next (instructionRun := instructionRun) (tail := tail) (by simp) tailPath
  exact ⟨run, path⟩

/-- Prepend any childless instruction without changing a direct-pause phase. -/
private theorem directPausePath_prepend_childless
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {instruction : Ninst} {body : Func} {out : Execution}
    (instructionRun : Ninst.RunCompiled sevm pre instruction post)
    (childless : ∀ operation : Xinst, instruction ≠ .exec operation)
    (tail : Func.RunCompiledTo fs sevm post body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca target
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (instruction ::: body) out,
      Func.RunCompiledTo.DirectPausePath ca target (phase := phase) run := by
  let run : Func.RunCompiledTo fs sevm pre (instruction ::: body) out :=
    .next instructionRun tail
  exact ⟨run, .next (instructionRun := instructionRun) (tail := tail)
    childless tailPath⟩

/-- Exact `PUSH` prepend for a direct-pause construction. -/
private theorem directPausePath_prepend_pushB256
    {ca : Adr} {target word : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {stack : List B256} {c G : Nat} {body : Func} {out : Execution}
    (hstack : pre.stack = stack)
    (hcost : pushCost word.toBytes.sig = c)
    (hgas : pre.gasLeft = G + c)
    (hroom : stack.length < 1024)
    (tail : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨word :: stack, pre.memory, G⟩) body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca target
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (Ninst.pushB256 word ::: body) out,
      Func.RunCompiledTo.DirectPausePath ca target (phase := phase) run := by
  subst stack
  apply directPausePath_prepend_childless
    (ca := ca) (target := target)
    (Ninst.runCompiled_pushB256 (sevm := sevm) (devm := pre) (w := word)
      (c := c) (G := G) hcost hgas hroom) (by
        unfold Ninst.pushB256
        simp) tail tailPath

/-- Exact two-instruction `tagTop` prepend. -/
private theorem directPausePath_prepend_tagTop
    {ca : Adr} {target x : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {region : Nat} {stack : List B256} {pushGas G : Nat}
    {body : Func} {out : Execution}
    (hpushCost : pushCost (regionWord region).toBytes.sig = pushGas)
    (hroom : stack.length < 1023)
    (tail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨slot region x :: stack, base.memory, G⟩) body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca target
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm
        (base.setMach ⟨x :: stack, base.memory,
          G + gVerylow + pushGas⟩)
        (tagTop region +++ body) out,
      Func.RunCompiledTo.DirectPausePath ca target (phase := phase) run := by
  let orPre := base.setMach ⟨regionWord region :: x :: stack,
    base.memory, G + gVerylow⟩
  have hor : Ninst.RunCompiled sevm orPre (.reg .or)
      (base.setMach ⟨slot region x :: stack, base.memory, G⟩) := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) (by rfl) rfl rfl
      (by change G + gVerylow = G + gVerylow; rfl) (by omega)
  rcases directPausePath_prepend_childless
      (ca := ca) (target := target) hor (by simp) tail tailPath with
    ⟨orRun, orPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := ca) (target := target) (word := regionWord region)
      (phase := phase) (stack := x :: stack) (c := pushGas)
      (pre := base.setMach ⟨x :: stack, base.memory,
        G + gVerylow + pushGas⟩) (G := G + gVerylow) rfl hpushCost rfl
      (by simp only [List.length_cons]; omega)
      (by simpa only [orPre, Devm.setMach_setMach,
        Devm.memory_setMach] using orRun)
      (by simpa only [orPre, Devm.setMach_setMach,
        Devm.memory_setMach] using orPath) with
    ⟨run, path⟩
  exact ⟨run, by simpa only [tagTop, prepend] using path⟩

/-- `SLOAD` as a CPS direct-pause path step.  The warmth-dependent base and
charge are exposed to the continuation together with every state projection
needed by later source code. -/
private theorem directPausePath_sload_step
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    {out : Execution}
    (hstack : devm.stack = k :: s)
    (hroom : s.length < 1024)
    (hvalue : devm.getStorVal sevm.currentTarget k = v)
    (hmemory : devm.memory = M)
    (hgas : gasColdSload ≤ devm.gasLeft)
    (hnext : ∀ (base : Devm) (c G : Nat),
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
        base.accessedStorageKeys →
      (∀ p : Adr × B256, p ∈ devm.accessedStorageKeys →
        p ∈ base.accessedStorageKeys) →
      (∀ (a : Adr) (k' : B256),
        base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedAddresses = devm.accessedAddresses →
      base.refundCounter = devm.refundCounter →
      base.logs = devm.logs →
      gasWarmAccess ≤ c → c ≤ gasColdSload →
      devm.gasLeft = G + c →
      ∃ tail : Func.RunCompiledTo fs sevm
          (base.setMach ⟨v :: s, M, G⟩) rest out,
        Func.RunCompiledTo.DirectPausePath ca target
          (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm devm
        (Func.next Ninst.sload rest) out,
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run := by
  subst hvalue
  subst M
  set base : Devm :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
      devm.accessedStorageKeys
    then devm else addAccessedStorageKey devm sevm.currentTarget k with hbase
  set c : Nat :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
      devm.accessedStorageKeys
    then gasWarmAccess else gasColdSload with hcost
  let G := devm.gasLeft - c
  have hkeyAccess :
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
        base.accessedStorageKeys :=
    mem_accessedStorageKeys_sload_of hbase.symm
  have haccessSubset : ∀ p : Adr × B256,
      p ∈ devm.accessedStorageKeys → p ∈ base.accessedStorageKeys :=
    fun _ hp => mem_accessedStorageKeys_sload_of_mem hbase.symm hp
  have hstorage : ∀ (a : Adr) (k' : B256),
      base.getStorVal a k' = devm.getStorVal a k' :=
    fun _ _ => getStorVal_sload_of hbase.symm
  have hbalances : ∀ a : Adr, base.getBal a = devm.getBal a := by
    intro a
    rw [hbase]
    split <;> rfl
  have hcode : ∀ a : Adr, base.getCode a = devm.getCode a := by
    intro a
    rw [hbase]
    split <;> rfl
  have haddresses : base.accessedAddresses = devm.accessedAddresses := by
    rw [hbase]
    split <;> rfl
  have hrefund : base.refundCounter = devm.refundCounter :=
    refundCounter_sload_of hbase.symm
  have hlogs : base.logs = devm.logs := logs_sload_of hbase.symm
  have hlower : gasWarmAccess ≤ c := (le_sload_cost_of hcost.symm).1
  have hupper : c ≤ gasColdSload := (le_sload_cost_of hcost.symm).2
  have hgasEq : devm.gasLeft = G + c := by
    dsimp only [G]
    omega
  rcases hnext base c G hkeyAccess haccessSubset hstorage hbalances
      hcode haddresses hrefund hlogs hlower hupper hgasEq with
    ⟨tail, tailPath⟩
  have instructionRun : Ninst.RunCompiled sevm devm Ninst.sload
      (base.setMach ⟨devm.getStorVal sevm.currentTarget k :: s,
        devm.memory, G⟩) := by
    exact Ninst.runCompiled_sload_of (base := base) (c := c) (G := G)
      hstack hbase.symm hcost.symm rfl (by omega) hroom
  let run : Func.RunCompiledTo fs sevm devm
      (Func.next Ninst.sload rest) out := .next instructionRun tail
  exact ⟨run, .next (instructionRun := instructionRun) (tail := tail)
    (by simp) tailPath⟩

/-- `MSTORE` as a CPS direct-pause path step, exposing the named written image
and successor gas account. -/
private theorem directPausePath_mstore_step
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i v : B256} {s : List B256} {c : Nat} {M : Mem} {rest : Func}
    {out : Execution}
    (hstack : devm.stack = i :: v :: s)
    (hmemory : devm.memory = M)
    (hcost : gVerylow + devm.extCost [⟨i.toNat, 32⟩] = c)
    (hgas : c ≤ devm.gasLeft)
    (hnext : ∀ (M' : Mem) (G : Nat),
      M.write i.toNat v.toBytes = M' →
      devm.gasLeft = G + c →
      ∃ tail : Func.RunCompiledTo fs sevm
          (devm.setMach ⟨s, M', G⟩) rest out,
        Func.RunCompiledTo.DirectPausePath ca target
          (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm devm
        (Func.next Ninst.mstore rest) out,
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run := by
  subst M
  let M' := devm.memory.write i.toNat v.toBytes
  let G := devm.gasLeft - c
  have hwrite : devm.memory.write i.toNat v.toBytes = M' := rfl
  have hgasEq : devm.gasLeft = G + c := by
    dsimp only [G]
    omega
  rcases hnext M' G hwrite hgasEq with ⟨tail, tailPath⟩
  have instructionRun : Ninst.RunCompiled sevm devm Ninst.mstore
      (devm.setMach ⟨s, M', G⟩) := by
    exact Ninst.runCompiled_mstore_of (G := G)
      (e := devm.extCost [⟨i.toNat, 32⟩]) hstack rfl (by omega) rfl
  let run : Func.RunCompiledTo fs sevm devm
      (Func.next Ninst.mstore rest) out := .next instructionRun tail
  exact ⟨run, .next (instructionRun := instructionRun) (tail := tail)
    (by simp) tailPath⟩

/-- Existential-output companion for `SLOAD`, used when the continuation
chooses the eventual revert state. -/
private theorem directPausePath_sload_revert_step
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    (hstack : devm.stack = k :: s)
    (hroom : s.length < 1024)
    (hvalue : devm.getStorVal sevm.currentTarget k = v)
    (hmemory : devm.memory = M)
    (hgas : gasColdSload ≤ devm.gasLeft)
    (hnext : ∀ (base : Devm) (c G : Nat),
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
        base.accessedStorageKeys →
      (∀ p : Adr × B256, p ∈ devm.accessedStorageKeys →
        p ∈ base.accessedStorageKeys) →
      (∀ (a : Adr) (k' : B256),
        base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedAddresses = devm.accessedAddresses →
      base.refundCounter = devm.refundCounter →
      base.logs = devm.logs →
      gasWarmAccess ≤ c → c ≤ gasColdSload →
      devm.gasLeft = G + c →
      ∃ raw, ∃ tail : Func.RunCompiledTo fs sevm
          (base.setMach ⟨v :: s, M, G⟩) rest (.error (.revert, raw)),
        raw.output = [] ∧
        Func.RunCompiledTo.DirectPausePath ca target
          (phase := phase) tail) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm devm
        (Func.next Ninst.sload rest) (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run := by
  subst hvalue
  subst M
  set base : Devm :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
      devm.accessedStorageKeys
    then devm else addAccessedStorageKey devm sevm.currentTarget k with hbase
  set c : Nat :=
    if (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
      devm.accessedStorageKeys
    then gasWarmAccess else gasColdSload with hcost
  let G := devm.gasLeft - c
  have hkeyAccess :
      (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
        base.accessedStorageKeys :=
    mem_accessedStorageKeys_sload_of hbase.symm
  have haccessSubset : ∀ p : Adr × B256,
      p ∈ devm.accessedStorageKeys → p ∈ base.accessedStorageKeys :=
    fun _ hp => mem_accessedStorageKeys_sload_of_mem hbase.symm hp
  have hstorage : ∀ (a : Adr) (k' : B256),
      base.getStorVal a k' = devm.getStorVal a k' :=
    fun _ _ => getStorVal_sload_of hbase.symm
  have hbalances : ∀ a : Adr, base.getBal a = devm.getBal a := by
    intro a
    rw [hbase]
    split <;> rfl
  have hcode : ∀ a : Adr, base.getCode a = devm.getCode a := by
    intro a
    rw [hbase]
    split <;> rfl
  have haddresses : base.accessedAddresses = devm.accessedAddresses := by
    rw [hbase]
    split <;> rfl
  have hrefund : base.refundCounter = devm.refundCounter :=
    refundCounter_sload_of hbase.symm
  have hlogs : base.logs = devm.logs := logs_sload_of hbase.symm
  have hlower : gasWarmAccess ≤ c := (le_sload_cost_of hcost.symm).1
  have hupper : c ≤ gasColdSload := (le_sload_cost_of hcost.symm).2
  have hgasEq : devm.gasLeft = G + c := by
    dsimp only [G]
    omega
  rcases hnext base c G hkeyAccess haccessSubset hstorage hbalances
      hcode haddresses hrefund hlogs hlower hupper hgasEq with
    ⟨raw, tail, rawOutput, tailPath⟩
  have instructionRun : Ninst.RunCompiled sevm devm Ninst.sload
      (base.setMach ⟨devm.getStorVal sevm.currentTarget k :: s,
        devm.memory, G⟩) := by
    exact Ninst.runCompiled_sload_of (base := base) (c := c) (G := G)
      hstack hbase.symm hcost.symm rfl (by omega) hroom
  let run : Func.RunCompiledTo fs sevm devm
      (Func.next Ninst.sload rest) (.error (.revert, raw)) :=
    .next instructionRun tail
  exact ⟨raw, run, rawOutput,
    .next (instructionRun := instructionRun) (tail := tail)
      (by simp) tailPath⟩

/-- Existential-output companion for `MSTORE`, used when its written memory
image determines the eventual revert state. -/
private theorem directPausePath_mstore_revert_step
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i v : B256} {s : List B256} {c : Nat} {M : Mem} {rest : Func}
    (hstack : devm.stack = i :: v :: s)
    (hmemory : devm.memory = M)
    (hcost : gVerylow + devm.extCost [⟨i.toNat, 32⟩] = c)
    (hgas : c ≤ devm.gasLeft)
    (hnext : ∀ (M' : Mem) (G : Nat),
      M.write i.toNat v.toBytes = M' →
      devm.gasLeft = G + c →
      ∃ raw, ∃ tail : Func.RunCompiledTo fs sevm
          (devm.setMach ⟨s, M', G⟩) rest (.error (.revert, raw)),
        raw.output = [] ∧
        Func.RunCompiledTo.DirectPausePath ca target
          (phase := phase) tail) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm devm
        (Func.next Ninst.mstore rest) (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run := by
  subst M
  let M' := devm.memory.write i.toNat v.toBytes
  let G := devm.gasLeft - c
  have hwrite : devm.memory.write i.toNat v.toBytes = M' := rfl
  have hgasEq : devm.gasLeft = G + c := by
    dsimp only [G]
    omega
  rcases hnext M' G hwrite hgasEq with
    ⟨raw, tail, rawOutput, tailPath⟩
  have instructionRun : Ninst.RunCompiled sevm devm Ninst.mstore
      (devm.setMach ⟨s, M', G⟩) := by
    exact Ninst.runCompiled_mstore_of (G := G)
      (e := devm.extCost [⟨i.toNat, 32⟩]) hstack rfl (by omega) rfl
  let run : Func.RunCompiledTo fs sevm devm
      (Func.next Ninst.mstore rest) (.error (.revert, raw)) :=
    .next instructionRun tail
  exact ⟨raw, run, rawOutput,
    .next (instructionRun := instructionRun) (tail := tail)
      (by simp) tailPath⟩

/-- Warm `SSTORE` in construction direction.  Its successor is written out so
the caller can continue in CPS without an execution premise. -/
private theorem directPausePath_prepend_warm_sstore
    {ca : Adr} {target k v : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {s : List B256} {c G : Nat} {rc : Int}
    {body : Func} {out : Execution}
    (hstack : devm.stack = k :: v :: s)
    (hwarm : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
      devm.accessedStorageKeys)
    (hsentry : gCallStipend < devm.gasLeft)
    (hstatic : sevm.isStatic = false)
    (hcost : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v = c)
    (hrefund : sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) devm.refundCounter = rc)
    (hgas : devm.gasLeft = G + c)
    (tail : Func.RunCompiledTo fs sevm
      (((devm.withRefundCounter rc).setStorVal sevm.currentTarget k v).setMach
        ⟨s, devm.memory, G⟩) body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca target
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm devm (.reg .sstore ::: body) out,
      Func.RunCompiledTo.DirectPausePath ca target (phase := phase) run := by
  apply directPausePath_prepend_sstore
    (ca := ca) (target := target)
    (Ninst.runCompiled_sstore_warm hstack hwarm hsentry hstatic
      hcost hrefund hgas) tail tailPath

/-- `SSTORE` on a warm key as a CPS direct-pause path step. -/
private theorem directPausePath_sstore_warm_step
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    {out : Execution}
    (hstack : devm.stack = k :: v :: s)
    (hwarm : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
      devm.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hmemory : devm.memory = M)
    (hgas : gasStorageSet ≤ devm.gasLeft)
    (hnext : ∀ (base : Devm) (c G : Nat),
      base.getStorVal sevm.currentTarget k = v →
      (∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
        base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.accessedAddresses = devm.accessedAddresses →
      base.logs = devm.logs →
      c ≤ gasStorageSet →
      devm.gasLeft = G + c →
      ∃ tail : Func.RunCompiledTo fs sevm
          (base.setMach ⟨s, M, G⟩) rest out,
        Func.RunCompiledTo.DirectPausePath ca target
          (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm devm
        (Func.next Ninst.sstore rest) out,
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run := by
  subst M
  have hbound : sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v ≤ gasStorageSet := by
    rw [sstoreValueCost]
    split_ifs <;> decide
  let base :=
    (devm.withRefundCounter (sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k)
      devm.refundCounter)).setStorVal sevm.currentTarget k v
  have hkey : base.getStorVal sevm.currentTarget k = v := by
    show (Devm.getStor _ sevm.currentTarget).get k = v
    rw [setStorVal_getStor_self, Stor.get_set_self]
  have hother : ∀ (a : Adr) (k' : B256),
      (a, k') ≠ (sevm.currentTarget, k) →
      base.getStorVal a k' = devm.getStorVal a k' := by
    intro a k' hne
    by_cases hadr : sevm.currentTarget = a
    · subst hadr
      have hkey' : k ≠ k' := fun h => hne (by rw [h])
      show (Devm.getStor _ sevm.currentTarget).get k' = _
      rw [setStorVal_getStor_self, Stor.get_set_ne _ hkey']
      rfl
    · show (Devm.getStor _ a).get k' = _
      have hoff : Devm.getStor base a = Devm.getStor devm a := by
        simp only [base, Devm.getStor, Devm.getAcct, Devm.setStorVal,
          Devm.withState, Devm.setWorld, State.setStorVal]
        simp only [Devm.state, State.get_set_ne _ hadr]
        rfl
      rw [hoff]
      rfl
  have hbalances : ∀ a : Adr, base.getBal a = devm.getBal a := by
    intro a
    have hbc := State.setStorVal_balCodeEq
      devm.state sevm.currentTarget k v
    exact (congrArg Prod.fst (congrFun hbc a)).symm
  have hcode : ∀ a : Adr, base.getCode a = devm.getCode a := by
    intro a
    have hbc := State.setStorVal_balCodeEq
      devm.state sevm.currentTarget k v
    exact (congrArg Prod.snd (congrFun hbc a)).symm
  have hkeys : base.accessedStorageKeys = devm.accessedStorageKeys := rfl
  have haddresses : base.accessedAddresses = devm.accessedAddresses := rfl
  have hlogs : base.logs = devm.logs := rfl
  let c := sstoreValueCost
    (getOrigStorVal sevm sevm.currentTarget k)
    (devm.getStorVal sevm.currentTarget k) v
  let G := devm.gasLeft - c
  have hgasEq : devm.gasLeft = G + c := by
    dsimp only [G, c]
    omega
  rcases hnext base c G hkey hother hbalances hcode hkeys haddresses hlogs
      hbound hgasEq with ⟨tail, tailPath⟩
  have instructionRun : Ninst.RunCompiled sevm devm (.reg .sstore)
      (base.setMach ⟨s, devm.memory, G⟩) := by
    dsimp only [base, G, c]
    exact Ninst.runCompiled_sstore_warm hstack hwarm
      (by simp only [gCallStipend, gasStorageSet] at *; omega)
      hstatic rfl rfl (by omega)
  let run : Func.RunCompiledTo fs sevm devm
      (Func.next Ninst.sstore rest) out :=
    .next instructionRun tail
  exact ⟨run, .next (instructionRun := instructionRun) (tail := tail)
    (by simp) tailPath⟩

/-- Existential-output companion used when the successor itself determines the
revert state. -/
private theorem directPausePath_sstore_warm_revert_step
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k v : B256} {s : List B256} {M : Mem} {rest : Func}
    (hstack : devm.stack = k :: v :: s)
    (hwarm : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
      devm.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hmemory : devm.memory = M)
    (hgas : gasStorageSet ≤ devm.gasLeft)
    (hnext : ∀ (base : Devm) (c G : Nat),
      base.getStorVal sevm.currentTarget k = v →
      (∀ (a : Adr) (k' : B256), (a, k') ≠ (sevm.currentTarget, k) →
        base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.accessedAddresses = devm.accessedAddresses →
      base.logs = devm.logs →
      c ≤ gasStorageSet →
      devm.gasLeft = G + c →
      ∃ raw, ∃ tail : Func.RunCompiledTo fs sevm
          (base.setMach ⟨s, M, G⟩) rest (.error (.revert, raw)),
        raw.output = [] ∧
        Func.RunCompiledTo.DirectPausePath ca target
          (phase := phase) tail) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm devm
        (Func.next Ninst.sstore rest)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run := by
  subst M
  have hbound : sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k) v ≤ gasStorageSet := by
    rw [sstoreValueCost]
    split_ifs <;> decide
  let base :=
    (devm.withRefundCounter (sstoreNewRefundCounter v
      (getOrigStorVal sevm sevm.currentTarget k)
      (devm.getStorVal sevm.currentTarget k)
      devm.refundCounter)).setStorVal sevm.currentTarget k v
  have hkey : base.getStorVal sevm.currentTarget k = v := by
    show (Devm.getStor _ sevm.currentTarget).get k = v
    rw [setStorVal_getStor_self, Stor.get_set_self]
  have hother : ∀ (a : Adr) (k' : B256),
      (a, k') ≠ (sevm.currentTarget, k) →
      base.getStorVal a k' = devm.getStorVal a k' := by
    intro a k' hne
    by_cases hadr : sevm.currentTarget = a
    · subst hadr
      have hkey' : k ≠ k' := fun h => hne (by rw [h])
      show (Devm.getStor _ sevm.currentTarget).get k' = _
      rw [setStorVal_getStor_self, Stor.get_set_ne _ hkey']
      rfl
    · show (Devm.getStor _ a).get k' = _
      have hoff : Devm.getStor base a = Devm.getStor devm a := by
        simp only [base, Devm.getStor, Devm.getAcct, Devm.setStorVal,
          Devm.withState, Devm.setWorld, State.setStorVal]
        simp only [Devm.state, State.get_set_ne _ hadr]
        rfl
      rw [hoff]
      rfl
  have hbalances : ∀ a : Adr, base.getBal a = devm.getBal a := by
    intro a
    have hbc := State.setStorVal_balCodeEq
      devm.state sevm.currentTarget k v
    exact (congrArg Prod.fst (congrFun hbc a)).symm
  have hcode : ∀ a : Adr, base.getCode a = devm.getCode a := by
    intro a
    have hbc := State.setStorVal_balCodeEq
      devm.state sevm.currentTarget k v
    exact (congrArg Prod.snd (congrFun hbc a)).symm
  have hkeys : base.accessedStorageKeys = devm.accessedStorageKeys := rfl
  have haddresses : base.accessedAddresses = devm.accessedAddresses := rfl
  have hlogs : base.logs = devm.logs := rfl
  let c := sstoreValueCost
    (getOrigStorVal sevm sevm.currentTarget k)
    (devm.getStorVal sevm.currentTarget k) v
  let G := devm.gasLeft - c
  have hgasEq : devm.gasLeft = G + c := by
    dsimp only [G, c]
    omega
  rcases hnext base c G hkey hother hbalances hcode hkeys haddresses hlogs
      hbound hgasEq with ⟨raw, tail, rawOutput, tailPath⟩
  have instructionRun : Ninst.RunCompiled sevm devm (.reg .sstore)
      (base.setMach ⟨s, devm.memory, G⟩) := by
    dsimp only [base, G, c]
    exact Ninst.runCompiled_sstore_warm hstack hwarm
      (by simp only [gCallStipend, gasStorageSet] at *; omega)
      hstatic rfl rfl (by omega)
  let run : Func.RunCompiledTo fs sevm devm
      (Func.next Ninst.sstore rest) (.error (.revert, raw)) :=
    .next instructionRun tail
  exact ⟨raw, run, rawOutput,
    .next (instructionRun := instructionRun) (tail := tail)
      (by simp) tailPath⟩

/-- Existential-output warm assignment-clear step.  This is the unique CPS
store constructor that changes the direct-pause certificate to `beforeWrite`. -/
private theorem directPausePath_assignment_zero_warm_revert_step
    {ca : Adr} {target : B256}
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {s : List B256} {M : Mem} {rest : Func}
    (howner : sevm.currentTarget = ca)
    (hstack : devm.stack = assignmentSlot target :: 0 :: s)
    (hwarm :
      (⟨sevm.currentTarget, assignmentSlot target⟩ : Adr × B256) ∈
        devm.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hmemory : devm.memory = M)
    (hgas : gasStorageSet ≤ devm.gasLeft)
    (hnext : ∀ (base : Devm) (c G : Nat),
      base.getStorVal sevm.currentTarget (assignmentSlot target) = 0 →
      (∀ (a : Adr) (k' : B256),
        (a, k') ≠ (sevm.currentTarget, assignmentSlot target) →
        base.getStorVal a k' = devm.getStorVal a k') →
      (∀ a : Adr, base.getBal a = devm.getBal a) →
      (∀ a : Adr, base.getCode a = devm.getCode a) →
      base.accessedStorageKeys = devm.accessedStorageKeys →
      base.accessedAddresses = devm.accessedAddresses →
      base.logs = devm.logs →
      c ≤ gasStorageSet →
      devm.gasLeft = G + c →
      ∃ raw, ∃ tail : Func.RunCompiledTo fs sevm
          (base.setMach ⟨s, M, G⟩) rest (.error (.revert, raw)),
        raw.output = [] ∧
        Func.RunCompiledTo.DirectPausePath ca target
          (phase := .beforeZeroCode) tail) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm devm
        (Func.next Ninst.sstore rest) (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := .beforeWrite) run := by
  subst M
  have hbound : sstoreValueCost
      (getOrigStorVal sevm sevm.currentTarget (assignmentSlot target))
      (devm.getStorVal sevm.currentTarget (assignmentSlot target)) 0 ≤
        gasStorageSet := by
    rw [sstoreValueCost]
    split_ifs <;> decide
  let base :=
    (devm.withRefundCounter (sstoreNewRefundCounter 0
      (getOrigStorVal sevm sevm.currentTarget (assignmentSlot target))
      (devm.getStorVal sevm.currentTarget (assignmentSlot target))
      devm.refundCounter)).setStorVal sevm.currentTarget
        (assignmentSlot target) 0
  have hkey : base.getStorVal sevm.currentTarget
      (assignmentSlot target) = 0 := by
    show (Devm.getStor _ sevm.currentTarget).get (assignmentSlot target) = 0
    rw [setStorVal_getStor_self, Stor.get_set_self]
  have hother : ∀ (a : Adr) (k' : B256),
      (a, k') ≠ (sevm.currentTarget, assignmentSlot target) →
      base.getStorVal a k' = devm.getStorVal a k' := by
    intro a k' hne
    by_cases hadr : sevm.currentTarget = a
    · subst hadr
      have hkey' : assignmentSlot target ≠ k' := fun h => hne (by rw [h])
      show (Devm.getStor _ sevm.currentTarget).get k' = _
      rw [setStorVal_getStor_self, Stor.get_set_ne _ hkey']
      rfl
    · show (Devm.getStor _ a).get k' = _
      have hoff : Devm.getStor base a = Devm.getStor devm a := by
        simp only [base, Devm.getStor, Devm.getAcct, Devm.setStorVal,
          Devm.withState, Devm.setWorld, State.setStorVal]
        simp only [Devm.state, State.get_set_ne _ hadr]
        rfl
      rw [hoff]
      rfl
  have hbalances : ∀ a : Adr, base.getBal a = devm.getBal a := by
    intro a
    have hbc := State.setStorVal_balCodeEq devm.state sevm.currentTarget
      (assignmentSlot target) 0
    exact (congrArg Prod.fst (congrFun hbc a)).symm
  have hcode : ∀ a : Adr, base.getCode a = devm.getCode a := by
    intro a
    have hbc := State.setStorVal_balCodeEq devm.state sevm.currentTarget
      (assignmentSlot target) 0
    exact (congrArg Prod.snd (congrFun hbc a)).symm
  have hkeys : base.accessedStorageKeys = devm.accessedStorageKeys := rfl
  have haddresses : base.accessedAddresses = devm.accessedAddresses := rfl
  have hlogs : base.logs = devm.logs := rfl
  let c := sstoreValueCost
    (getOrigStorVal sevm sevm.currentTarget (assignmentSlot target))
    (devm.getStorVal sevm.currentTarget (assignmentSlot target)) 0
  let G := devm.gasLeft - c
  have hgasEq : devm.gasLeft = G + c := by
    dsimp only [G, c]
    omega
  rcases hnext base c G hkey hother hbalances hcode hkeys haddresses hlogs
      hbound hgasEq with ⟨raw, tail, rawOutput, tailPath⟩
  have instructionRun : Ninst.RunCompiled sevm devm (.reg .sstore)
      (base.setMach ⟨s, devm.memory, G⟩) := by
    dsimp only [base, G, c]
    exact Ninst.runCompiled_sstore_warm hstack hwarm
      (by simp only [gCallStipend, gasStorageSet] at *; omega)
      hstatic rfl rfl (by omega)
  have hpopped : Stack.Pop [assignmentSlot target, 0] devm.stack
      (base.setMach ⟨s, devm.memory, G⟩).stack := by
    rw [hstack]
    rfl
  let run : Func.RunCompiledTo fs sevm devm
      (Func.next Ninst.sstore rest) (.error (.revert, raw)) :=
    .next instructionRun tail
  exact ⟨raw, run, rawOutput,
    .write (instructionRun := instructionRun) (tail := tail)
      howner hpopped tailPath⟩

/-- Prepend the distinguished assignment-clear write.  Unlike ordinary removal
writes, this is the unique transition that changes the certificate phase. -/
private theorem directPausePath_prepend_assignment_zero_sstore
    {ca : Adr} {target : B256} {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {body : Func} {out : Execution}
    (instructionRun : Ninst.RunCompiled sevm pre (.reg .sstore) post)
    (howner : sevm.currentTarget = ca)
    (hpopped : Stack.Pop [assignmentSlot target, 0] pre.stack post.stack)
    (tail : Func.RunCompiledTo fs sevm post body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca target
      (phase := .beforeZeroCode) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (.reg .sstore ::: body) out,
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := .beforeWrite) run := by
  let run : Func.RunCompiledTo fs sevm pre (.reg .sstore ::: body) out :=
    .next instructionRun tail
  have path : Func.RunCompiledTo.DirectPausePath ca target
      (phase := .beforeWrite) run :=
    .write (instructionRun := instructionRun) (tail := tail)
      howner hpopped tailPath
  exact ⟨run, path⟩

set_option linter.unusedVariables false in
private inductive Exec.DirectPausePath (ca : Adr) (target : B256) :
    ∀ {phase : DirectPausePhase} {pc : Nat} {sevm : Sevm}
      {pre : Devm} {out : Execution}, Exec pc sevm pre out → Prop
  | halt {pc sevm pre out terminal}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .halt out}
      (terminalAt : Linst.At sevm.code pc terminal) :
      Exec.DirectPausePath ca target
        (phase := .afterZeroCode) (.halt step)
  | cont {pc nextPc sevm pre post out phase}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .cont nextPc post}
      {tail : Exec nextPc sevm post out}
      (rootChildless : ∀ operation : Xinst,
        ¬ Ninst.At sevm.code pc (.exec operation))
      (tailPath : Exec.DirectPausePath ca target
        (phase := phase) tail) :
      Exec.DirectPausePath ca target
        (phase := phase) (.cont step tail)
  | zeroCode {pc sevm pre post out}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .cont (pc + 1) post}
      {tail : Exec (pc + 1) sevm post out}
      (instructionAt : Ninst.At sevm.code pc (.reg .extcodesize))
      (instructionRun : Ninst.RunCompiled sevm pre
        (.reg .extcodesize) post)
      (stack : ∃ rest, pre.stack = target :: rest)
      (codeSize : (pre.getCode target.toAdr).size = 0)
      (tailPath : Exec.DirectPausePath ca target
        (phase := .afterZeroCode) tail) :
      Exec.DirectPausePath ca target
        (phase := .beforeZeroCode) (.cont step tail)
  | write {pc sevm pre post out}
      {step : Evm.step ⟨pc, sevm, pre⟩ = .cont (pc + 1) post}
      {tail : Exec (pc + 1) sevm post out}
      (instructionAt : Ninst.At sevm.code pc (.reg .sstore))
      (instructionRun : Ninst.RunCompiled sevm pre (.reg .sstore) post)
      (owner : sevm.currentTarget = ca)
      (popped : Stack.Pop [assignmentSlot target, 0]
        pre.stack post.stack)
      (tailPath : Exec.DirectPausePath ca target
        (phase := .beforeZeroCode) tail) :
      Exec.DirectPausePath ca target
        (phase := .beforeWrite) (.cont step tail)

private lemma Ninst.exists_exec_directPausePath
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    {instruction : Ninst} {out : Execution}
    (instructionAt : Ninst.At sevm.code pc instruction)
    (instructionRun : Ninst.RunCompiled sevm pre instruction post)
    (instructionChildless : ∀ operation : Xinst,
      instruction ≠ .exec operation)
    {tail : Exec (pc + instruction.size) sevm post out}
    (tailPath : Exec.DirectPausePath ca target
      (phase := phase) tail) :
    ∃ run : Exec pc sevm pre out,
      Exec.DirectPausePath ca target (phase := phase) run := by
  have rootChildless : ∀ operation : Xinst,
      ¬ Ninst.At sevm.code pc (.exec operation) := by
    intro operation operationAt
    exact instructionChildless operation
      (Ninst.at_unique instructionAt operationAt)
  have evmStep : Evm.step ⟨pc, sevm, pre⟩ =
      Ninst.step ⟨pc, sevm, pre⟩ instruction :=
    Evm.step_next instructionAt
  rcases instructionRun with ⟨slot, filled, steps⟩
  have stepRun := steps pc
  cases instruction with
  | reg operation =>
      rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
      have step : Evm.step ⟨pc, sevm, pre⟩ = .cont (pc + 1) post := by
        rw [evmStep, Ninst.step_reg, ← stepRun.2]
        rfl
      exact ⟨.cont step tail, .cont rootChildless tailPath⟩
  | push bytes length =>
      rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at stepRun
      have step : Evm.step ⟨pc, sevm, pre⟩ =
          .cont (pc + Ninst.size (.push bytes length)) post := by
        rw [evmStep, Ninst.step_push, ← stepRun.2]
        rfl
      exact ⟨.cont step tail, .cont rootChildless tailPath⟩
  | exec operation =>
      exact (instructionChildless operation rfl).elim

private theorem Func.RunCompiledTo.exists_exec_directPausePath :
    ∀ {f₀ : Func} {fs' : List Func} {sevm : Sevm} {fs : List Func}
      {pre : Devm} {body : Func} {out : Execution}
      {ca : Adr} {target : B256} {phase : DirectPausePhase}
      (run : Func.RunCompiledTo fs sevm pre body out),
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run →
      some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩ →
      fs = f₀ :: fs' →
      ∀ pc,
        subcode sevm.code.toList pc
          (Func.compile (table 0 (f₀ :: fs')) pc body) →
        noPushBefore sevm.code pc 32 = true →
        ∃ execution : Exec pc sevm pre out,
          Exec.DirectPausePath ca target (phase := phase) execution := by
  intro f₀ fs' sevm fs pre body out ca target phase run path
  induction path with
  | @zero certFs certSevm certPre certPost left right certOut
      certPhase room pop tail tailPath ih =>
      intro compiled tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpiAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_zero_steps pushAt jumpiAt locAt room pop with
        ⟨pushStep, jumpStep⟩
      rcases ih compiled tableEq (pc + 4) leftSub leftNoPush with
        ⟨leftRun, leftPath⟩
      have pushChildless : ∀ operation : Xinst,
          ¬ Ninst.At certSevm.code pc (.exec operation) := by
        intro operation operationAt
        have impossible := Ninst.at_unique pushAt operationAt
        cases impossible
      have jumpChildless : ∀ operation : Xinst,
          ¬ Ninst.At certSevm.code (pc + 3) (.exec operation) :=
        fun _ operationAt => operationAt.false_of_jinstAt jumpiAt
      exact ⟨.cont pushStep (.cont jumpStep leftRun),
        .cont pushChildless (.cont jumpChildless leftPath)⟩
  | @succ certFs certSevm certPre certPost left right certOut
      certPhase word nonzero room pop tail tailPath ih =>
      intro compiled tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpiAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_succ_steps pushAt jumpiAt jumpdestAt jumpable
        locAt nonzero room pop with
        ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih compiled tableEq (loc + 1) rightSub rightNoPush with
        ⟨rightRun, rightPath⟩
      have pushChildless : ∀ operation : Xinst,
          ¬ Ninst.At certSevm.code pc (.exec operation) := by
        intro operation operationAt
        have impossible := Ninst.at_unique pushAt operationAt
        cases impossible
      have jumpChildless : ∀ operation : Xinst,
          ¬ Ninst.At certSevm.code (pc + 3) (.exec operation) :=
        fun _ operationAt => operationAt.false_of_jinstAt jumpiAt
      have jumpdestChildless : ∀ operation : Xinst,
          ¬ Ninst.At certSevm.code loc (.exec operation) :=
        fun _ operationAt => operationAt.false_of_jinstAt jumpdestAt
      exact ⟨.cont pushStep (.cont jumpStep
          (.cont jumpdestStep rightRun)),
        .cont pushChildless (.cont jumpChildless
          (.cont jumpdestChildless rightPath))⟩
  | @last certFs certSevm certPre terminal certOut terminalRun =>
      intro compiled tableEq pc sub noPush
      have terminalAt := Linst.at_of_slice sub
      have step : Evm.step ⟨pc, certSevm, certPre⟩ = .halt certOut := by
        rw [Evm.step_last terminalAt]
        exact congrArg Step.halt terminalRun
      exact ⟨.halt step, .halt terminalAt⟩
  | @next certFs certSevm certPre certPost instruction certBody
      certOut certPhase instructionRun tail childless tailPath ih =>
      intro compiled tableEq pc sub noPush
      rcases Func.noPushBefore_next sub noPush with
        ⟨tailNoPush, tailSub⟩
      rcases of_subcode sub with ⟨code, compileEq, slice⟩
      rcases of_bind_eq_some compileEq with
        ⟨tailCode, tailCompileEq, codeEq⟩
      simp [pure] at codeEq
      rw [← codeEq] at slice
      have instructionAt : Ninst.At certSevm.code pc instruction :=
        Ninst.at_of_slice (List.slice_prefix slice)
      rcases ih compiled tableEq _ tailSub tailNoPush with
        ⟨tailRun, tailExecutionPath⟩
      exact Ninst.exists_exec_directPausePath instructionAt instructionRun
        childless tailExecutionPath
  | @call certFs certSevm certPre certPost index certBody certOut
      certPhase lookup room burn tail tailPath ih =>
      intro compiled tableEq pc sub noPush
      subst tableEq
      rcases subcode_compile_call sub with
        ⟨loc, compiledBody, tableLookup, locBound, pushAt, jumpAt⟩
      have selected := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) tableLookup)
      rw [lookup] at selected
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at selected
      subst selected
      rcases subcode_of_get?_eq_some compiled tableLookup with
        ⟨jumpdestAt, bodySub⟩
      have bodyJumpable := Prog.jumpable_of_get?_table compiled tableLookup
      rcases pushAt with ⟨length, pushAt⟩
      rcases Evm.call_steps (le := length) pushAt jumpAt jumpdestAt
        bodyJumpable.1 locBound room burn with
        ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih compiled rfl (loc + 1) bodySub bodyJumpable.2 with
        ⟨bodyRun, bodyPath⟩
      have pushChildless : ∀ operation : Xinst,
          ¬ Ninst.At certSevm.code pc (.exec operation) := by
        intro operation operationAt
        have impossible := Ninst.at_unique pushAt operationAt
        cases impossible
      have jumpChildless : ∀ operation : Xinst,
          ¬ Ninst.At certSevm.code (pc + 3) (.exec operation) :=
        fun _ operationAt => operationAt.false_of_jinstAt jumpAt
      have jumpdestChildless : ∀ operation : Xinst,
          ¬ Ninst.At certSevm.code loc (.exec operation) :=
        fun _ operationAt => operationAt.false_of_jinstAt jumpdestAt
      exact ⟨.cont pushStep (.cont jumpStep
          (.cont jumpdestStep bodyRun)),
        .cont pushChildless (.cont jumpChildless
          (.cont jumpdestChildless bodyPath))⟩
  | @zeroCode certFs certSevm certPre certPost certBody certOut
      instructionRun tail stack codeSize tailPath ih =>
      intro compiled tableEq pc sub noPush
      rcases Func.noPushBefore_next sub noPush with
        ⟨tailNoPush, tailSub⟩
      rcases of_subcode sub with ⟨code, compileEq, slice⟩
      rcases of_bind_eq_some compileEq with
        ⟨tailCode, tailCompileEq, codeEq⟩
      simp [pure] at codeEq
      rw [← codeEq] at slice
      have instructionAt : Ninst.At certSevm.code pc (.reg .extcodesize) :=
        Ninst.at_of_slice (List.slice_prefix slice)
      rcases ih compiled tableEq _ tailSub tailNoPush with
        ⟨tailRun, tailExecutionPath⟩
      have instructionRun' := instructionRun
      rcases instructionRun with ⟨slot, filled, steps⟩
      have stepRun := steps pc
      rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
      have evmStep : Evm.step ⟨pc, certSevm, certPre⟩ =
          Ninst.step ⟨pc, certSevm, certPre⟩ (.reg .extcodesize) :=
        Evm.step_next instructionAt
      have step : Evm.step ⟨pc, certSevm, certPre⟩ =
          .cont (pc + 1) certPost := by
        rw [evmStep, Ninst.step_reg, ← stepRun.2]
        rfl
      exact ⟨.cont step tailRun,
        .zeroCode instructionAt instructionRun' stack codeSize
          tailExecutionPath⟩
  | @write certFs certSevm certPre certPost certBody certOut
      instructionRun tail owner popped tailPath ih =>
      intro compiled tableEq pc sub noPush
      rcases Func.noPushBefore_next sub noPush with
        ⟨tailNoPush, tailSub⟩
      rcases of_subcode sub with ⟨code, compileEq, slice⟩
      rcases of_bind_eq_some compileEq with
        ⟨tailCode, tailCompileEq, codeEq⟩
      simp [pure] at codeEq
      rw [← codeEq] at slice
      have instructionAt : Ninst.At certSevm.code pc (.reg .sstore) :=
        Ninst.at_of_slice (List.slice_prefix slice)
      rcases ih compiled tableEq _ tailSub tailNoPush with
        ⟨tailRun, tailExecutionPath⟩
      have instructionRun' := instructionRun
      rcases instructionRun with ⟨slot, filled, steps⟩
      have stepRun := steps pc
      rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
      have evmStep : Evm.step ⟨pc, certSevm, certPre⟩ =
          Ninst.step ⟨pc, certSevm, certPre⟩ (.reg .sstore) :=
        Evm.step_next instructionAt
      have step : Evm.step ⟨pc, certSevm, certPre⟩ =
          .cont (pc + 1) certPost := by
        rw [evmStep, Ninst.step_reg, ← stepRun.2]
        rfl
      exact ⟨.cont step tailRun,
        .write instructionAt instructionRun' owner popped
          tailExecutionPath⟩

/-- Strict raw-node order, specialized to the two marked direct-pause nodes. -/
def Exec.RawBefore {root : Exec.Deriv}
    (left right : Exec.Deriv) : Prop :=
  ∃ before middle after,
    Exec.rawNodes root.exc = before ++ left :: middle ++ right :: after

/-- Rebase an exact instruction occurrence along a proved raw-node inclusion. -/
private def Exec.NinstOccurrence.rebase
    {inner outer : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence inner)
    (reached : occurrence.node ∈ Exec.rawNodes outer.exc) :
    Exec.NinstOccurrence outer :=
  { occurrence with reached := reached }

/-- Rebase an exact successful write along a proved raw-node inclusion. -/
private def Exec.SuccessfulSstoreOccurrence.rebase
    {inner outer : Exec.Deriv}
    (write : Exec.SuccessfulSstoreOccurrence inner)
    (reached : write.occurrence.node ∈ Exec.rawNodes outer.exc) :
    Exec.SuccessfulSstoreOccurrence outer :=
  { write with occurrence := { write.occurrence with reached := reached } }

/-- Every node selected by the direct-pause certificate excludes both external
call opcodes. -/
private theorem Exec.DirectPausePath.noCallOrStaticcallAt
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (path : Exec.DirectPausePath ca target (phase := phase) run) :
    ∀ node ∈ Exec.rawNodes run,
      (¬ Ninst.At node.sevm.code node.pc (.exec .call)) ∧
      (¬ Ninst.At node.sevm.code node.pc (.exec .staticcall)) := by
  induction path with
  | halt terminalAt =>
      intro node reached
      simp only [Exec.rawNodes, List.mem_cons, List.not_mem_nil,
        or_false] at reached
      subst node
      exact ⟨fun callAt => callAt.false_of_linstAt terminalAt,
        fun callAt => callAt.false_of_linstAt terminalAt⟩
  | cont rootChildless tailPath ih =>
      intro node reached
      simp only [Exec.rawNodes, List.mem_cons] at reached
      rcases reached with rfl | reached
      · exact ⟨rootChildless .call, rootChildless .staticcall⟩
      · exact ih node reached
  | zeroCode instructionAt instructionRun stack codeSize tailPath ih =>
      intro node reached
      simp only [Exec.rawNodes, List.mem_cons] at reached
      rcases reached with rfl | reached
      · constructor <;> intro callAt
        · cases Ninst.at_unique instructionAt callAt
        · cases Ninst.at_unique instructionAt callAt
      · exact ih node reached
  | write instructionAt instructionRun owner popped tailPath ih =>
      intro node reached
      simp only [Exec.rawNodes, List.mem_cons] at reached
      rcases reached with rfl | reached
      · constructor <;> intro callAt
        · cases Ninst.at_unique instructionAt callAt
        · cases Ninst.at_unique instructionAt callAt
      · exact ih node reached

/-- Occurrence-facing form of the path's universal CALL/STATICCALL exclusion. -/
private theorem Exec.DirectPausePath.noCallOrStaticcall
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (path : Exec.DirectPausePath ca target (phase := phase) run) :
    ∀ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      occurrence.instruction ≠ .exec .call ∧
      occurrence.instruction ≠ .exec .staticcall := by
  intro occurrence
  have excluded := path.noCallOrStaticcallAt
    occurrence.node occurrence.reached
  exact ⟨fun instructionEq => excluded.1 (instructionEq ▸ occurrence.decoded),
    fun instructionEq => excluded.2 (instructionEq ▸ occurrence.decoded)⟩

/-- Extract the marked target `EXTCODESIZE` from the selected middle phase. -/
private theorem Exec.DirectPausePath.exists_zeroCodeOccurrence_of_eq
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (path : Exec.DirectPausePath ca target
      (phase := phase) run)
    (hphase : phase = .beforeZeroCode) :
    ∃ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      occurrence.instruction = .reg .extcodesize ∧
      (∃ rest, occurrence.node.devm.stack = target :: rest) ∧
      (occurrence.node.devm.getCode target.toAdr).size = 0 := by
  induction path with
  | halt terminalAt => cases hphase
  | @cont pathPc pathNextPc pathSevm pathPre pathPost pathOut pathPhase
      step tail rootChildless tailPath ih =>
      rcases ih hphase with ⟨occurrence, instructionEq, stack, codeSize⟩
      have liftedReached : occurrence.node ∈
          Exec.rawNodes (Exec.cont step tail) := by
        simp only [Exec.rawNodes, List.mem_cons]
        exact Or.inr occurrence.reached
      let root : Exec.Deriv :=
        ⟨pathPc, pathSevm, pathPre, pathOut, Exec.cont step tail⟩
      let lifted : Exec.NinstOccurrence root :=
        { occurrence with reached := liftedReached }
      exact ⟨lifted, instructionEq, stack, codeSize⟩
  | @zeroCode pathPc pathSevm pathPre pathPost pathOut step tail
      instructionAt instructionRun stack codeSize tailPath ih =>
      rcases instructionRun with ⟨slot, filled, steps⟩
      let root : Exec.Deriv :=
        ⟨pathPc, pathSevm, pathPre, pathOut, Exec.cont step tail⟩
      let occurrence : Exec.NinstOccurrence root :=
        { node := root
          instruction := .reg .extcodesize
          slot := slot
          stepResult := .ok pathPost
          reached := Exec.mem_rawNodes_self _
          decoded := instructionAt
          filled := filled
          stepRun := by
            simpa [root] using steps pathPc }
      refine ⟨occurrence, rfl, ?_, ?_⟩
      · simpa [occurrence, root] using stack
      · simpa [occurrence, root] using codeSize
  | write instructionAt instructionRun owner popped tailPath ih =>
      cases hphase

/-- Extract the marked target `EXTCODESIZE` from the middle phase. -/
private theorem Exec.DirectPausePath.exists_zeroCodeOccurrence
    {ca : Adr} {target : B256}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (path : Exec.DirectPausePath ca target
      (phase := .beforeZeroCode) run) :
    ∃ occurrence : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      occurrence.instruction = .reg .extcodesize ∧
      (∃ rest, occurrence.node.devm.stack = target :: rest) ∧
      (occurrence.node.devm.getCode target.toAdr).size = 0 :=
  path.exists_zeroCodeOccurrence_of_eq rfl

/-- Extract the assignment-clear write and its later target-zero code check. -/
private theorem Exec.DirectPausePath.exists_writeBeforeZeroCode_of_eq
    {ca : Adr} {target : B256} {phase : DirectPausePhase}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (path : Exec.DirectPausePath ca target (phase := phase) run)
    (hphase : phase = .beforeWrite) :
    ∃ write : Exec.SuccessfulSstoreOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      write.storageOwner = ca ∧
      write.key = assignmentSlot target ∧
      write.value = 0 ∧
      ∃ zeroCode : Exec.NinstOccurrence
          (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
        zeroCode.instruction = .reg .extcodesize ∧
        (∃ rest, zeroCode.node.devm.stack = target :: rest) ∧
        (zeroCode.node.devm.getCode target.toAdr).size = 0 ∧
        Exec.RawBefore
          (root := ⟨pc, sevm, pre, out, run⟩)
          write.occurrence.node zeroCode.node := by
  induction path with
  | halt terminalAt => cases hphase
  | @cont pathPc pathNextPc pathSevm pathPre pathPost pathOut pathPhase
      step tail rootChildless tailPath ih =>
      rcases ih hphase with
        ⟨write, writeOwner, writeKey, writeValue, zeroCode,
          zeroInstruction, zeroStack, zeroSize, order⟩
      have writeReached : write.occurrence.node ∈
          Exec.rawNodes (Exec.cont step tail) := by
        simp only [Exec.rawNodes, List.mem_cons]
        exact Or.inr write.occurrence.reached
      have zeroReached : zeroCode.node ∈
          Exec.rawNodes (Exec.cont step tail) := by
        simp only [Exec.rawNodes, List.mem_cons]
        exact Or.inr zeroCode.reached
      let root : Exec.Deriv :=
        ⟨pathPc, pathSevm, pathPre, pathOut, Exec.cont step tail⟩
      let liftedWrite : Exec.SuccessfulSstoreOccurrence root :=
        { write with occurrence :=
            { write.occurrence with reached := writeReached } }
      let liftedZero : Exec.NinstOccurrence root :=
        { zeroCode with reached := zeroReached }
      rcases order with ⟨before, middle, after, order⟩
      have liftedOrder : Exec.RawBefore (root := root)
          liftedWrite.occurrence.node liftedZero.node := by
        refine ⟨root :: before, middle, after, ?_⟩
        simp only [root, Exec.rawNodes, List.cons_append]
        exact congrArg (root :: ·) order
      exact ⟨liftedWrite, writeOwner, writeKey, writeValue,
        liftedZero, zeroInstruction, zeroStack, zeroSize, liftedOrder⟩
  | zeroCode instructionAt instructionRun stack codeSize tailPath ih =>
      cases hphase
  | @write pathPc pathSevm pathPre pathPost pathOut step tail
      instructionAt instructionRun owner popped tailPath ih =>
      rcases tailPath.exists_zeroCodeOccurrence with
        ⟨zeroCode, zeroInstruction, zeroStack, zeroSize⟩
      have zeroReached : zeroCode.node ∈
          Exec.rawNodes (Exec.cont step tail) := by
        simp only [Exec.rawNodes, List.mem_cons]
        exact Or.inr zeroCode.reached
      let root : Exec.Deriv :=
        ⟨pathPc, pathSevm, pathPre, pathOut, Exec.cont step tail⟩
      let liftedZero : Exec.NinstOccurrence root :=
        { zeroCode with reached := zeroReached }
      rcases instructionRun with ⟨slot, filled, steps⟩
      let occurrence : Exec.NinstOccurrence root :=
        { node := root
          instruction := .reg .sstore
          slot := slot
          stepResult := .ok pathPost
          reached := Exec.mem_rawNodes_self _
          decoded := instructionAt
          filled := filled
          stepRun := by simpa [root] using steps pathPc }
      let write : Exec.SuccessfulSstoreOccurrence root :=
        { occurrence := occurrence
          instruction_eq := rfl
          stepPost := pathPost
          stepSuccess := rfl
          key := assignmentSlot target
          value := 0
          popped := by simpa [occurrence, root] using popped }
      rcases zeroCode.rawNodes_decomposition with
        ⟨before, after, zeroDecomposition⟩
      have order : Exec.RawBefore (root := root)
          write.occurrence.node liftedZero.node := by
        refine ⟨[], before, after, ?_⟩
        simp only [root, write, occurrence, liftedZero, List.nil_append,
          Exec.rawNodes]
        exact congrArg (root :: ·) zeroDecomposition
      refine ⟨write, ?_, rfl, rfl, liftedZero,
        zeroInstruction, zeroStack, zeroSize, order⟩
      simpa [Exec.SuccessfulSstoreOccurrence.storageOwner,
        write, occurrence, root] using owner

/-- Complete raw evidence exposed by a before-write execution certificate. -/
private theorem Exec.DirectPausePath.beforeWriteEvidence
    {ca : Adr} {target : B256}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (path : Exec.DirectPausePath ca target (phase := .beforeWrite) run) :
    (∃ write : Exec.SuccessfulSstoreOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      write.storageOwner = ca ∧
      write.key = assignmentSlot target ∧
      write.value = 0 ∧
      ∃ zeroCode : Exec.NinstOccurrence
          (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
        zeroCode.instruction = .reg .extcodesize ∧
        (∃ rest, zeroCode.node.devm.stack = target :: rest) ∧
        (zeroCode.node.devm.getCode target.toAdr).size = 0 ∧
        Exec.RawBefore
          (root := ⟨pc, sevm, pre, out, run⟩)
          write.occurrence.node zeroCode.node) ∧
      ∀ occurrence : Exec.NinstOccurrence
          (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
        occurrence.instruction ≠ .exec .call ∧
        occurrence.instruction ≠ .exec .staticcall :=
  ⟨exists_writeBeforeZeroCode_of_eq path rfl,
    path.noCallOrStaticcall⟩

/-- Compiler-facing transport of the complete direct-pause raw evidence. -/
private theorem Func.RunCompiledTo.exists_exec_directPauseEvidence
    {f₀ : Func} {fs' : List Func} {sevm : Sevm} {fs : List Func}
    {pre : Devm} {body : Func} {out : Execution}
    {ca : Adr} {target : B256}
    (run : Func.RunCompiledTo fs sevm pre body out)
    (path : Func.RunCompiledTo.DirectPausePath ca target
      (phase := .beforeWrite) run)
    (compiled : some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩)
    (tableEq : fs = f₀ :: fs')
    (pc : Nat)
    (sub : subcode sevm.code.toList pc
      (Func.compile (table 0 (f₀ :: fs')) pc body))
    (noPush : noPushBefore sevm.code pc 32 = true) :
    ∃ execution : Exec pc sevm pre out,
      ((∃ write : Exec.SuccessfulSstoreOccurrence
          (⟨pc, sevm, pre, out, execution⟩ : Exec.Deriv),
        write.storageOwner = ca ∧
        write.key = assignmentSlot target ∧
        write.value = 0 ∧
        ∃ zeroCode : Exec.NinstOccurrence
            (⟨pc, sevm, pre, out, execution⟩ : Exec.Deriv),
          zeroCode.instruction = .reg .extcodesize ∧
          (∃ rest, zeroCode.node.devm.stack = target :: rest) ∧
          (zeroCode.node.devm.getCode target.toAdr).size = 0 ∧
          Exec.RawBefore
            (root := ⟨pc, sevm, pre, out, execution⟩)
            write.occurrence.node zeroCode.node) ∧
        ∀ occurrence : Exec.NinstOccurrence
            (⟨pc, sevm, pre, out, execution⟩ : Exec.Deriv),
          occurrence.instruction ≠ .exec .call ∧
          occurrence.instruction ≠ .exec .staticcall) := by
  rcases Func.RunCompiledTo.exists_exec_directPausePath run path compiled
      tableEq pc sub noPush with ⟨execution, executionPath⟩
  exact ⟨execution,
    ⟨Exec.DirectPausePath.exists_writeBeforeZeroCode_of_eq
        executionPath rfl,
      executionPath.noCallOrStaticcall⟩⟩

/-- A raw top-level revert forces the settled direct-message result to carry an
error flag.  This exposes the premise used by the existing rollback theorem. -/
private theorem ProcessMessage.error_isSome_of_raw_revert
    {msg : Msg} {post raw : Devm} {pc : Nat} {sevm : Sevm} {pre : Devm}
    (hprocess : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, .error (.revert, raw)⟩) (.ok post)) :
    post.error.isSome := by
  have hsettle := (RunFrame.some_inv hprocess).2
  simp only [Frame.ofCall, Frame.settle, Frame.settleMsg] at hsettle
  simp [executeCode.handleError] at hsettle
  have herr : (raw.withError (some .revert)).error.isSome = true := by rfl
  unfold processMessage.settle at hsettle
  simp only [bind, Except.bind] at hsettle
  rw [if_pos herr] at hsettle
  have hpost := Except.ok.inj hsettle
  rw [hpost]
  rfl

/-- Exact warm/cold account-access alternatives for the marked code-size read. -/
private inductive PauseAfterSetAccessCase
    (pre : Devm) (target : B256) : Nat → Devm → Prop
  | warm (haccess : target.toAdr ∈ pre.accessedAddresses) :
      PauseAfterSetAccessCase pre target gasWarmAccess pre
  | cold (haccess : target.toAdr ∉ pre.accessedAddresses) :
      PauseAfterSetAccessCase pre target gasColdAccountAccess
        (addAccessedAddress pre target.toAdr)

/-- Exact source cost of the target-zero prefix and its empty-revert branch. -/
private def pauseAfterSetZeroCodeCost
    (pre : Devm) (codeCost : Nat) : Nat :=
  gVerylow +
    (gVerylow + pre.extCost [⟨(targetWord * 32).toNat, 32⟩]) +
    gVerylow + codeCost + gVerylow +
    (gVerylow + gHigh + gJumpdest) +
    (gVerylow + gMid + gJumpdest) +
    (gBase + gBase)

/-- The zero-code `pauseAfterSet` branch reaches the exact empty-output revert
and carries the middle-phase direct-pause certificate. -/
private theorem pauseAfterSet_zeroCode_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre codeBase : Devm}
    {img : Bytes} {stack : List B256} {target : B256}
    {codeCost G : Nat}
    (hstack : pre.stack = stack)
    (_hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : PauseAfterSetAccessCase pre target codeCost codeBase)
    (hgas : pre.gasLeft = G + pauseAfterSetZeroCodeCost pre codeCost)
    (hroom : stack.length < 1022)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert) :
    let M := (pre.memory.read (targetWord * 32).toNat 32).2
    let raw := (codeBase.setMach ⟨target :: stack, M, G⟩).withOutput []
    ∃ run : Func.RunCompiledTo fs sevm pre pauseAfterSet
        (.error (.revert, raw)),
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let offset : B256 := targetWord * 32
  let M : Mem := (pre.memory.read offset.toNat 32).2
  let loadCost : Nat := gVerylow + pre.extCost [⟨offset.toNat, 32⟩]
  let suffixCost : Nat := gVerylow + (gVerylow + gHigh + gJumpdest) +
    (gVerylow + gMid + gJumpdest) + (gBase + gBase)
  let raw := (codeBase.setMach ⟨target :: stack, M, G⟩).withOutput []
  have hoffset : offset ≠ 0 := by
    dsimp only [offset]
    decide
  have htargetValue : Bytes.toB256
      (pre.memory.read offset.toNat 32).1 = target := by
    rw [Mem.Reads.read hr]
    exact htargetRead
  have hpush : Ninst.RunCompiled sevm pre (Ninst.pushB256 offset)
      (pre.setMach ⟨offset :: stack, pre.memory,
        G + loadCost + gVerylow + codeCost + suffixCost⟩) := by
    simpa only [hstack] using Ninst.runCompiled_pushB256
      (sevm := sevm) (devm := pre) (w := offset) (c := gVerylow)
      (G := G + loadCost + gVerylow + codeCost + suffixCost)
      (pushCost_of_ne_zero hoffset) (by
        rw [hgas]
        dsimp [pauseAfterSetZeroCodeCost, loadCost, suffixCost, offset]
        omega) (by rw [hstack]; omega)
  have hload : Ninst.RunCompiled sevm
      (pre.setMach ⟨offset :: stack, pre.memory,
        G + loadCost + gVerylow + codeCost + suffixCost⟩)
      mload
      (pre.setMach ⟨target :: stack, M,
        G + gVerylow + codeCost + suffixCost⟩) := by
    simpa only [Devm.setMach_setMach] using Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := pre.setMach ⟨offset :: stack, pre.memory,
        G + loadCost + gVerylow + codeCost + suffixCost⟩)
      (i := offset) (v := target) (s := stack) (c := loadCost)
      (G := G + gVerylow + codeCost + suffixCost) (M := M)
      rfl rfl htargetValue rfl (by
        simp only [Devm.gasLeft_setMach]
        omega) (by omega)
  have hdup : Ninst.RunCompiled sevm
      (pre.setMach ⟨target :: stack, M,
        G + gVerylow + codeCost + suffixCost⟩)
      (dup 0)
      (pre.setMach ⟨target :: target :: stack, M,
        G + codeCost + suffixCost⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Ninst.runCompiled_dup
      (sevm := sevm)
      (devm := pre.setMach ⟨target :: stack, M,
        G + gVerylow + codeCost + suffixCost⟩)
      (n := 0) (w := target) (G := G + codeCost + suffixCost)
      rfl (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
  have hext : Ninst.RunCompiled sevm
      (pre.setMach ⟨target :: target :: stack, M,
        G + codeCost + suffixCost⟩)
      extcodesize
      (codeBase.setMach ⟨0 :: target :: stack, M,
        G + suffixCost⟩) := by
    cases haccess with
    | warm hwarm =>
        simpa only [Devm.setMach_setMach, Devm.memory_setMach] using
          Ninst.runCompiled_extcodesize_warm
            (sevm := sevm)
            (devm := pre.setMach ⟨target :: target :: stack, M,
              G + gasWarmAccess + suffixCost⟩)
            (x := target) (v := 0) (s := target :: stack)
            (G := G + suffixCost) rfl
            (by change target.toAdr ∈ pre.accessedAddresses; exact hwarm)
            (by
              change Nat.toB256 (pre.getCode target.toAdr).size = 0
              rw [hcodeSize]
              decide)
            (by simp only [Devm.gasLeft_setMach]; omega)
            (by simp only [List.length_cons]; omega)
    | cold hcold =>
        have hc := Ninst.runCompiled_extcodesize_cold
            (sevm := sevm)
            (devm := pre.setMach ⟨target :: target :: stack, M,
              G + gasColdAccountAccess + suffixCost⟩)
            (x := target) (v := 0) (s := target :: stack)
            (G := G + suffixCost) rfl
            (by change target.toAdr ∉ pre.accessedAddresses; exact hcold)
            (by
              change Nat.toB256 (pre.getCode target.toAdr).size = 0
              rw [hcodeSize]
              decide)
            (by simp only [Devm.gasLeft_setMach]; omega)
            (by simp only [List.length_cons]; omega)
        change Ninst.RunCompiled sevm _ extcodesize
          ((addAccessedAddress
            (pre.setMach ⟨target :: target :: stack, M,
              G + gasColdAccountAccess + suffixCost⟩) target.toAdr).setMach
            ⟨0 :: target :: stack, M, G + suffixCost⟩)
        exact hc
  have hiszero : Ninst.RunCompiled sevm
      (codeBase.setMach ⟨0 :: target :: stack, M,
        G + suffixCost⟩)
      iszero
      (codeBase.setMach ⟨1 :: target :: stack, M,
        G + (gVerylow + gHigh + gJumpdest) +
          (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩) := by
    exact Ninst.runCompiled_unary (by rintro ⟨⟩) rfl rfl rfl (by
        simp only [Devm.gasLeft_setMach]
        dsimp only [suffixCost]
        omega) (by
          simp only [List.length_cons]
          omega)
  have hrev : Func.RunCompiledTo fs sevm
      (codeBase.setMach ⟨target :: stack, M, G + (gBase + gBase)⟩)
      Func.revert (.error (.revert, raw)) := by
    simpa only [raw, Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach, Devm.gasLeft_setMach] using
      Func.runCompiledTo_revert_func
        (fs := fs) (sevm := sevm)
        (devm := codeBase.setMach
          ⟨target :: stack, M, G + (gBase + gBase)⟩)
        (G := G) rfl (by
          change (target :: stack).length < 1023
          simp only [List.length_cons]
          omega)
  have hrevPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .afterZeroCode) hrev := by
    cases hrev with
    | next firstRun firstTail =>
        refine .next (instructionRun := firstRun) (tail := firstTail)
          (by unfold Ninst.pushB256; simp) ?_
        cases firstTail with
        | next secondRun secondTail =>
            refine .next (instructionRun := secondRun) (tail := secondTail)
              (by unfold Ninst.pushB256; simp) ?_
            cases secondTail with
            | last terminalRun => exact .last (terminalRun := terminalRun)
  have hcallRoom :
      (codeBase.setMach ⟨target :: stack, M,
        G + (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩).stack.length <
        1024 := by
    simp only [Devm.stack_setMach, List.length_cons]
    omega
  have hcallBurn : Devm.BurnBy (gVerylow + gMid + gJumpdest)
      (codeBase.setMach ⟨target :: stack, M,
        G + (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩)
      (codeBase.setMach ⟨target :: stack, M, G + (gBase + gBase)⟩) := by
    convert Devm.burnBy_setMach_gas (devm :=
      codeBase.setMach ⟨target :: stack, M,
        G + (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩)
      (cost := gVerylow + gMid + gJumpdest)
      (G := G + (gBase + gBase)) (by
        simp only [Devm.gasLeft_setMach]
        omega) using 1
    all_goals rfl
  let hcall : Func.RunCompiledTo fs sevm
      (codeBase.setMach ⟨target :: stack, M,
        G + (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩)
      (.call emptyRevertSlot) (.error (.revert, raw)) :=
    .call hemptyLookup hcallRoom hcallBurn hrev
  have hcallPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .afterZeroCode) hcall :=
    .call (lookup := hemptyLookup) (room := hcallRoom)
      (burn := hcallBurn) (tail := hrev) hrevPath
  have hbranchRoom :
      (codeBase.setMach ⟨1 :: target :: stack, M,
        G + (gVerylow + gHigh + gJumpdest) +
          (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩).stack.length <
        1024 := by
    simp only [Devm.stack_setMach, List.length_cons]
    omega
  have hbranchPop : Devm.PopBurnBy [1]
      (gVerylow + gHigh + gJumpdest)
      (codeBase.setMach ⟨1 :: target :: stack, M,
        G + (gVerylow + gHigh + gJumpdest) +
          (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩)
      (codeBase.setMach ⟨target :: stack, M,
        G + (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Devm.popBurnBy_setMach
        (devm := codeBase.setMach ⟨1 :: target :: stack, M,
          G + (gVerylow + gHigh + gJumpdest) +
            (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩)
        (x := (1 : B256)) (s := target :: stack) rfl (by
          simp only [Devm.gasLeft_setMach]
          omega)
  let hbranch : Func.RunCompiledTo fs sevm
      (codeBase.setMach ⟨1 :: target :: stack, M,
        G + (gVerylow + gHigh + gJumpdest) +
          (gVerylow + gMid + gJumpdest) + (gBase + gBase)⟩)
      ((.call emptyRevertSlot) <?>
        (pop ::: pushB256 pauseForSelector ::: mstoreAt 8 +++
          loadWord durationWord +++ mstoreAt 9 +++
          pushList [0, 0, 36, 0x11c, 0] +++ loadWord targetWord +++
          gas ::: call ::: iszero :::
          ((.call bubbleRevertSlot) <?>
            (pushB256 isPausedSelector ::: mstoreAt 8 +++
              pushList [32, 0, 4, 0x11c] +++ loadWord targetWord +++
              gas ::: staticcall ::: iszero :::
              ((.call bubbleRevertSlot) <?> decodePausedResult)))))
      (.error (.revert, raw)) :=
    .succ (by decide : (1 : B256) ≠ 0) hbranchRoom hbranchPop hcall
  have hbranchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .afterZeroCode) hbranch :=
    .succ (nonzero := (by decide : (1 : B256) ≠ 0))
      (room := hbranchRoom) (pop := hbranchPop) (tail := hcall) hcallPath
  let iszeroTail := Func.RunCompiledTo.next hiszero hbranch
  have iszeroPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .afterZeroCode) iszeroTail :=
    .next (instructionRun := hiszero) (tail := hbranch) (by simp) hbranchPath
  let extTail := Func.RunCompiledTo.next hext iszeroTail
  have extPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) extTail := by
    refine .zeroCode (instructionRun := hext) (tail := iszeroTail)
      ⟨target :: stack, rfl⟩ ?_ iszeroPath
    simpa only [Devm.getCode_setMach] using hcodeSize
  let dupTail := Func.RunCompiledTo.next hdup extTail
  have dupPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) dupTail :=
    .next (instructionRun := hdup) (tail := extTail) (by simp) extPath
  let loadTail := Func.RunCompiledTo.next hload dupTail
  have loadPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) loadTail :=
    .next (instructionRun := hload) (tail := dupTail) (by simp) dupPath
  let hrun : Func.RunCompiledTo fs sevm pre pauseAfterSet
      (.error (.revert, raw)) := by
    simp only [pauseAfterSet]
    exact .next hpush loadTail
  have hrunPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) hrun :=
    .next (instructionRun := hpush) (tail := loadTail)
      (by unfold Ninst.pushB256; simp) loadPath
  exact ⟨hrun, hrunPath⟩

/-- Cost of one `loadWord`, with its current memory image explicit. -/
private def finishLoadWordCost (devm : Devm) (word : B256) : Nat :=
  pushCost ((word * 32).toBytes.sig) +
    gVerylow + devm.extCost [⟨(word * 32).toNat, 32⟩]

/-- Concrete `loadWord` prepend, transporting the direct-pause phase without
assuming an execution premise for the load itself. -/
private theorem loadWord_prepend_directPause
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {word value markedTarget : B256} {stack : List B256} {G : Nat}
    {rest : Func} {out : Execution} {phase : DirectPausePhase}
    (hstack : pre.stack = stack)
    (hvalue : Bytes.toB256
      (pre.memory.read (word * 32).toNat 32).1 = value)
    (hgas : pre.gasLeft = G + finishLoadWordCost pre word)
    (hroom : stack.length < 1023)
    (tail : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨value :: stack,
        (pre.memory.read (word * 32).toNat 32).2, G⟩) rest out)
    (tailPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget markedTarget
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (loadWord word +++ rest) out,
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget markedTarget
        (phase := phase) run := by
  let offset : B256 := word * 32
  let M : Mem := (pre.memory.read offset.toNat 32).2
  let loadCost : Nat := gVerylow + pre.extCost [⟨offset.toNat, 32⟩]
  have hpush : Ninst.RunCompiled sevm pre (Ninst.pushB256 offset)
      (pre.setMach ⟨offset :: stack, pre.memory, G + loadCost⟩) := by
    simpa only [hstack] using Ninst.runCompiled_pushB256
      (sevm := sevm) (devm := pre) (w := offset)
      (c := pushCost offset.toBytes.sig) (G := G + loadCost) rfl (by
        rw [hgas]
        dsimp [finishLoadWordCost, loadCost, offset]
        omega) (by rw [hstack]; omega)
  have hload : Ninst.RunCompiled sevm
      (pre.setMach ⟨offset :: stack, pre.memory, G + loadCost⟩) mload
      (pre.setMach ⟨value :: stack, M, G⟩) := by
    simpa only [Devm.setMach_setMach] using Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := pre.setMach ⟨offset :: stack, pre.memory, G + loadCost⟩)
      (i := offset) (v := value) (s := stack) (c := loadCost)
      (G := G) (M := M) rfl rfl hvalue rfl (by
        simp only [Devm.gasLeft_setMach]) (by omega)
  let loadTail := Func.RunCompiledTo.next hload tail
  have loadPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget markedTarget
      (phase := phase) loadTail :=
    .next (instructionRun := hload) (tail := tail) (by simp) tailPath
  let run : Func.RunCompiledTo fs sevm pre (loadWord word +++ rest) out := by
    change Func.RunCompiledTo fs sevm pre
      (.next (Ninst.pushB256 offset) (.next mload rest)) out
    exact .next hpush loadTail
  exact ⟨run, .next (instructionRun := hpush) (tail := loadTail)
    (by unfold Ninst.pushB256; simp) loadPath⟩

/-- Package the warm/cold account-access split around the exact target-zero
`pauseAfterSet` construction. -/
private theorem pauseAfterSet_zeroCode_runCompiledTo_by_access
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256} {target : B256} {G : Nat}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hgas : pre.gasLeft = G + pauseAfterSetZeroCodeCost pre
      (accessCost target.toAdr pre.accessedAddresses))
    (hroom : stack.length < 1022)
    (hstack : pre.stack = stack)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre pauseAfterSet
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  rcases haccess with hwarm | hcold
  · have hcost : accessCost target.toAdr pre.accessedAddresses =
        gasWarmAccess := by simp [accessCost, hwarm]
    rw [hcost] at hgas
    rcases pauseAfterSet_zeroCode_runCompiledTo hstack hwf hr htargetRead
        hcodeSize (.warm hwarm) hgas hroom hemptyLookup with ⟨run, path⟩
    let raw := (pre.setMach ⟨target :: stack,
      (pre.memory.read (targetWord * 32).toNat 32).2, G⟩).withOutput []
    exact ⟨raw, run, rfl, path⟩
  · let coldBase := addAccessedAddress pre target.toAdr
    have hcost : accessCost target.toAdr pre.accessedAddresses =
        gasColdAccountAccess := by simp [accessCost, hcold]
    rw [hcost] at hgas
    rcases pauseAfterSet_zeroCode_runCompiledTo hstack hwf hr htargetRead
        hcodeSize (.cold hcold) hgas hroom hemptyLookup with ⟨run, path⟩
    let raw := (coldBase.setMach ⟨target :: stack,
      (pre.memory.read (targetWord * 32).toNat 32).2, G⟩).withOutput []
    exact ⟨raw, run, rfl, path⟩

private def finishSetPauserPauseCallCost
    (pre : Devm) (target : B256) : Nat :=
  let pausePre := pre.setMach ⟨[], pre.memory, 0⟩
  (gVerylow + gMid + gJumpdest) +
    pauseAfterSetZeroCodeCost pausePre
      (accessCost target.toAdr pre.accessedAddresses)

/-- Exact internal call into the target-zero `pauseAfterSet` branch. -/
private theorem finishSetPauser_pause_call_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {img : Bytes} {stack : List B256} {target : B256} {G : Nat}
    (hwf : Mem.Wf base.memory)
    (hr : Mem.Reads base.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcodeSize : (base.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ base.accessedAddresses ∨
      target.toAdr ∉ base.accessedAddresses)
    (hroom : stack.length < 1019)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm
        (base.setMach ⟨stack, base.memory,
          G + finishSetPauserPauseCallCost base target⟩)
        (.call pauseAfterSetSlot) (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let pausePre₀ := base.setMach ⟨[], base.memory, 0⟩
  let pauseCost := pauseAfterSetZeroCodeCost pausePre₀
    (accessCost target.toAdr base.accessedAddresses)
  let callCost := gVerylow + gMid + gJumpdest
  let pausePre := base.setMach ⟨stack, base.memory, G + pauseCost⟩
  have hpauseAccess : target.toAdr ∈ pausePre.accessedAddresses ∨
      target.toAdr ∉ pausePre.accessedAddresses := by
    change target.toAdr ∈ base.accessedAddresses ∨
      target.toAdr ∉ base.accessedAddresses
    exact haccess
  have hpauseGas : pausePre.gasLeft = G +
      pauseAfterSetZeroCodeCost pausePre
        (accessCost target.toAdr pausePre.accessedAddresses) := by
    rw [show pausePre.accessedAddresses = base.accessedAddresses by rfl]
    simp only [pausePre, Devm.gasLeft_setMach]
    dsimp only [pauseCost, pausePre₀]
    simp only [pauseAfterSetZeroCodeCost, Devm.extCost,
      Devm.memory_setMach]
  rcases pauseAfterSet_zeroCode_runCompiledTo_by_access
      (pre := pausePre) (stack := stack) (G := G)
      hwf hr htargetRead
      (by change (base.getCode target.toAdr).size = 0; exact hcodeSize)
      hpauseAccess hpauseGas (by omega) rfl hemptyLookup with
    ⟨raw, hpause, rawOutput, hpausePath⟩
  have hpauseRoom :
      (base.setMach ⟨stack, base.memory,
        G + pauseCost + callCost⟩).stack.length < 1024 := by
    simp only [Devm.stack_setMach]
    omega
  have hpauseBurn : Devm.BurnBy callCost
      (base.setMach ⟨stack, base.memory,
        G + pauseCost + callCost⟩) pausePre := by
    dsimp only [callCost, pausePre]
    convert Devm.burnBy_setMach_gas
      (devm := base.setMach ⟨stack, base.memory,
        G + pauseCost + (gVerylow + gMid + gJumpdest)⟩)
      (cost := gVerylow + gMid + gJumpdest) (G := G + pauseCost)
      (by simp only [Devm.gasLeft_setMach]) using 1
    all_goals rfl
  let run := Func.RunCompiledTo.call hpauseLookup hpauseRoom hpauseBurn hpause
  have path : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) run :=
    .call (lookup := hpauseLookup) (room := hpauseRoom)
      (burn := hpauseBurn) (tail := hpause) hpausePath
  have hstartGas : G + finishSetPauserPauseCallCost base target =
      G + pauseCost + callCost := by
    dsimp only [finishSetPauserPauseCallCost, pauseCost, pausePre₀, callCost]
    omega
  rw [hstartGas]
  exact ⟨raw, run, rawOutput, path⟩

private def finishSetPauserPauseBranchCost
    (pre : Devm) (target : B256) : Nat :=
  gVerylow + (gVerylow + gHigh) +
    finishSetPauserPauseCallCost pre target

/-- The saved continuation is one: `ISZERO` produces zero and the conditional
takes its zero branch into the internal pause call. -/
private theorem finishSetPauser_pause_branch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {img : Bytes} {stack : List B256} {target : B256} {G : Nat}
    (hwf : Mem.Wf base.memory)
    (hr : Mem.Reads base.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcodeSize : (base.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ base.accessedAddresses ∨
      target.toAdr ∉ base.accessedAddresses)
    (hroom : stack.length < 1019)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm
        (base.setMach ⟨1 :: stack, base.memory,
          G + finishSetPauserPauseBranchCost base target⟩)
        (iszero ::: ((.call registerAfterSetSlot) <?>
          (.call pauseAfterSetSlot))) (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let callCost := finishSetPauserPauseCallCost base target
  rcases finishSetPauser_pause_call_runCompiledTo
      (sevm := sevm) (base := base) (G := G)
      hwf hr htargetRead hcodeSize haccess hroom
      hemptyLookup hpauseLookup with
    ⟨raw, hpauseCall, rawOutput, hpauseCallPath⟩
  let branchCost := gVerylow + gHigh
  have hbranchRoom :
      (base.setMach ⟨0 :: stack, base.memory,
        G + callCost + branchCost⟩).stack.length < 1024 := by
    simp only [Devm.stack_setMach, List.length_cons]
    omega
  have hbranchPop : Devm.PopBurnBy [0] (gVerylow + gHigh)
      (base.setMach ⟨0 :: stack, base.memory,
        G + callCost + branchCost⟩)
      (base.setMach ⟨stack, base.memory, G + callCost⟩) := by
    dsimp only [branchCost]
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Devm.popBurnBy_setMach
        (devm := base.setMach ⟨0 :: stack, base.memory,
          G + callCost + (gVerylow + gHigh)⟩)
        (x := (0 : B256)) (s := stack) rfl
        (by simp only [Devm.gasLeft_setMach])
  let hbranch : Func.RunCompiledTo fs sevm
      (base.setMach ⟨0 :: stack, base.memory,
        G + callCost + branchCost⟩)
      ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))
      (.error (.revert, raw)) :=
    Func.RunCompiledTo.zero hbranchRoom hbranchPop hpauseCall
  have hbranchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) hbranch :=
    .zero (room := hbranchRoom) (pop := hbranchPop)
      (tail := hpauseCall) hpauseCallPath
  have hiszero : Ninst.RunCompiled sevm
      (base.setMach ⟨1 :: stack, base.memory,
        G + callCost + branchCost + gVerylow⟩) iszero
      (base.setMach ⟨0 :: stack, base.memory,
        G + callCost + branchCost⟩) := by
    exact Ninst.runCompiled_unary (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach])
      (by omega)
  let run := Func.RunCompiledTo.next hiszero hbranch
  have path : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) run :=
    .next (instructionRun := hiszero) (tail := hbranch) (by simp) hbranchPath
  have hstartGas : G + finishSetPauserPauseBranchCost base target =
      G + callCost + branchCost + gVerylow := by
    dsimp only [finishSetPauserPauseBranchCost, callCost, branchCost]
    omega
  rw [hstartGas]
  exact ⟨raw, run, rawOutput, path⟩

private def finishSetPauserPauseTerminal : Func :=
  loadWord continuationWord +++ iszero :::
  ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))

private def finishSetPauserPauseTerminalCost
    (pre : Devm) (target : B256) : Nat :=
  let M := (pre.memory.read (continuationWord * 32).toNat 32).2
  let postLoad := pre.setMach ⟨[], M, 0⟩
  finishLoadWordCost pre continuationWord +
    finishSetPauserPauseBranchCost postLoad target

/-- Exact continuation load followed by the saved-one pause branch. -/
private theorem finishSetPauser_pause_terminal_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {img : Bytes} {stack : List B256} {target : B256} {G : Nat}
    (hwf : Mem.Wf base.memory)
    (hr : Mem.Reads base.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hcodeSize : (base.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ base.accessedAddresses ∨
      target.toAdr ∉ base.accessedAddresses)
    (hroom : stack.length < 1019)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm
        (base.setMach ⟨stack, base.memory,
          G + finishSetPauserPauseTerminalCost base target⟩)
        finishSetPauserPauseTerminal (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M := (base.memory.read (continuationWord * 32).toNat 32).2
  let postLoad := base.setMach ⟨[], M, 0⟩
  let branchCost := finishSetPauserPauseBranchCost postLoad target
  have hwfM : Mem.Wf M := hwf.extend _ _
  have hrM : Mem.Reads M img := Mem.Reads.extend hr _ _
  have hcontinuation : Bytes.toB256
      (base.memory.read (continuationWord * 32).toNat 32).1 = 1 := by
    rw [Mem.Reads.read hr]
    exact hcontinuationRead
  rcases finishSetPauser_pause_branch_runCompiledTo
      (sevm := sevm) (base := postLoad) (G := G) hwfM hrM htargetRead
      (by change (base.getCode target.toAdr).size = 0; exact hcodeSize)
      (by
        change target.toAdr ∈ base.accessedAddresses ∨
          target.toAdr ∉ base.accessedAddresses
        exact haccess)
      hroom hemptyLookup hpauseLookup with
    ⟨raw, hbranch, rawOutput, hbranchPath⟩
  have hloadGas :
      (base.setMach ⟨stack, base.memory,
        G + branchCost + finishLoadWordCost base continuationWord⟩).gasLeft =
      (G + branchCost) + finishLoadWordCost
        (base.setMach ⟨stack, base.memory,
          G + branchCost + finishLoadWordCost base continuationWord⟩)
        continuationWord := by
    simp only [Devm.gasLeft_setMach]
    simp only [finishLoadWordCost, Devm.extCost, Devm.memory_setMach]
  rcases loadWord_prepend_directPause
      (pre := base.setMach ⟨stack, base.memory,
        G + branchCost + finishLoadWordCost base continuationWord⟩)
      (markedTarget := target) (hstack := rfl) hcontinuation hloadGas
      (by simp only [Devm.stack_setMach]; omega) hbranch hbranchPath with
    ⟨run, path⟩
  have hstartGas : G + finishSetPauserPauseTerminalCost base target =
      G + branchCost + finishLoadWordCost base continuationWord := by
    dsimp only [finishSetPauserPauseTerminalCost, branchCost, postLoad, M]
    omega
  rw [hstartGas]
  exact ⟨raw,
    by simpa [finishSetPauserPauseTerminal] using run,
    rawOutput,
    by simpa [finishSetPauserPauseTerminal] using path⟩

private def finishSetPauserPauseSuffix : Func :=
  pushB256 pauserSetEvent ::: logWith 3 0 0 +++
  finishSetPauserPauseTerminal

private def finishSetPauserPauseSuffixCost
    (pre : Devm) (target : B256) : Nat :=
  pushCost pauserSetEvent.toBytes.sig +
    pushCost (((0 : B256) * 32).toBytes.sig) +
    pushCost (((0 : B256) * 32).toBytes.sig) +
    (gLog + gLogtopic * 4) +
    finishSetPauserPauseTerminalCost pre target

/-- Correct `PauserSet` prefix: two zero pushes and `LOG4` consume the event
signature and all three indexed values, leaving the original stack. -/
private theorem finishSetPauser_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target : B256} {G : Nat}
    (hwf : Mem.Wf base.memory)
    (hr : Mem.Reads base.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hcodeSize : (base.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ base.accessedAddresses ∨
      target.toAdr ∉ base.accessedAddresses)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm
        (base.setMach ⟨target :: previousPauser :: newPauser :: stack,
          base.memory, G + finishSetPauserPauseSuffixCost base target⟩)
        finishSetPauserPauseSuffix (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let entry : Log := ⟨sevm.currentTarget,
    [pauserSetEvent, target, previousPauser, newPauser], []⟩
  let logged := base.addLog entry
  let terminalCost := finishSetPauserPauseTerminalCost logged target
  have hterminalCost : terminalCost =
      finishSetPauserPauseTerminalCost base target := by
    rfl
  rcases finishSetPauser_pause_terminal_runCompiledTo
      (sevm := sevm) (base := logged) (G := G)
      (by change Mem.Wf base.memory; exact hwf)
      (by change Mem.Reads base.memory img; exact hr)
      htargetRead hcontinuationRead
      (by change (base.getCode target.toAdr).size = 0; exact hcodeSize)
      (by
        change target.toAdr ∈ base.accessedAddresses ∨
          target.toAdr ∉ base.accessedAddresses
        exact haccess)
      hroom hemptyLookup hpauseLookup with
    ⟨raw, hterminal, rawOutput, hterminalPath⟩
  let zeroWord : B256 := 0 * 32
  have hzeroWord : zeroWord = 0 := by
    rfl
  let logCost := gLog + gLogtopic * 4
  have hlog : Ninst.RunCompiled sevm
      (base.setMach ⟨zeroWord :: zeroWord :: pauserSetEvent :: target ::
        previousPauser :: newPauser :: stack, base.memory,
        G + terminalCost + logCost⟩)
      (.reg (.log 4))
      (logged.setMach ⟨stack, base.memory, G + terminalCost⟩) := by
    simpa [logged, entry, Devm.addLog, liftMachMetaPure, Devm.setMach] using
      Ninst.runCompiled_log_of
        (sevm := sevm)
        (devm := base.setMach
          ⟨zeroWord :: zeroWord :: pauserSetEvent :: target ::
            previousPauser :: newPauser :: stack, base.memory,
            G + terminalCost + logCost⟩)
        (n := 4) (i := zeroWord) (sz := zeroWord)
        (topics := [pauserSetEvent, target, previousPauser, newPauser])
        (s := stack) (c := logCost) (G := G + terminalCost)
        (M := base.memory) (data := []) rfl rfl hstatic (by
          rw [hzeroWord]
          dsimp only [logCost]
          simp only [B256.toNat_zero, Devm.extCost_empty_window]
          omega) (by
          rw [hzeroWord]
          rfl) (by
          rw [hzeroWord]
          rfl) (by simp only [Devm.gasLeft_setMach])
  let hlogTail := Func.RunCompiledTo.next hlog hterminal
  have hlogPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) hlogTail :=
    .next (instructionRun := hlog) (tail := hterminal)
      (by simp) hterminalPath
  let zeroCost := pushCost zeroWord.toBytes.sig
  let eventCost := pushCost pauserSetEvent.toBytes.sig
  let pushedGas := G + terminalCost + logCost
  have hzero₂ : Ninst.RunCompiled sevm
      (base.setMach ⟨zeroWord :: pauserSetEvent :: target :: previousPauser ::
        newPauser :: stack, base.memory, pushedGas + zeroCost⟩)
      (Ninst.pushB256 zeroWord)
      (base.setMach ⟨zeroWord :: zeroWord :: pauserSetEvent :: target ::
        previousPauser :: newPauser :: stack, base.memory, pushedGas⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Ninst.runCompiled_pushB256
      (sevm := sevm)
      (devm := base.setMach
        ⟨zeroWord :: pauserSetEvent :: target :: previousPauser ::
          newPauser :: stack, base.memory, pushedGas + zeroCost⟩)
      (w := zeroWord) (c := zeroCost) (G := pushedGas) rfl
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
  let hzero₂Tail := Func.RunCompiledTo.next hzero₂ hlogTail
  have hzero₂Path : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) hzero₂Tail :=
    .next (instructionRun := hzero₂) (tail := hlogTail)
      (by unfold Ninst.pushB256; simp) hlogPath
  have hzero₁ : Ninst.RunCompiled sevm
      (base.setMach ⟨pauserSetEvent :: target :: previousPauser ::
        newPauser :: stack, base.memory, pushedGas + zeroCost + zeroCost⟩)
      (Ninst.pushB256 zeroWord)
      (base.setMach ⟨zeroWord :: pauserSetEvent :: target :: previousPauser ::
        newPauser :: stack, base.memory, pushedGas + zeroCost⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Ninst.runCompiled_pushB256
      (sevm := sevm)
      (devm := base.setMach
        ⟨pauserSetEvent :: target :: previousPauser :: newPauser :: stack,
          base.memory, pushedGas + zeroCost + zeroCost⟩)
      (w := zeroWord) (c := zeroCost) (G := pushedGas + zeroCost) rfl
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
  let hzero₁Tail := Func.RunCompiledTo.next hzero₁ hzero₂Tail
  have hzero₁Path : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) hzero₁Tail :=
    .next (instructionRun := hzero₁) (tail := hzero₂Tail)
      (by unfold Ninst.pushB256; simp) hzero₂Path
  have hevent : Ninst.RunCompiled sevm
      (base.setMach ⟨target :: previousPauser :: newPauser :: stack,
        base.memory, pushedGas + zeroCost + zeroCost + eventCost⟩)
      (Ninst.pushB256 pauserSetEvent)
      (base.setMach ⟨pauserSetEvent :: target :: previousPauser ::
        newPauser :: stack, base.memory, pushedGas + zeroCost + zeroCost⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Ninst.runCompiled_pushB256
      (sevm := sevm)
      (devm := base.setMach
        ⟨target :: previousPauser :: newPauser :: stack, base.memory,
          pushedGas + zeroCost + zeroCost + eventCost⟩)
      (w := pauserSetEvent) (c := eventCost)
      (G := pushedGas + zeroCost + zeroCost) rfl
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
  let heventTail := Func.RunCompiledTo.next hevent hzero₁Tail
  have heventPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) heventTail :=
    .next (instructionRun := hevent) (tail := hzero₁Tail)
      (by unfold Ninst.pushB256; simp) hzero₁Path
  have hstartGas : G + finishSetPauserPauseSuffixCost base target =
      pushedGas + zeroCost + zeroCost + eventCost := by
    dsimp only [finishSetPauserPauseSuffixCost, pushedGas, logCost,
      zeroCost, eventCost, zeroWord]
    rw [hterminalCost]
    omega
  rw [hstartGas]
  let run : Func.RunCompiledTo fs sevm
      (base.setMach ⟨target :: previousPauser :: newPauser :: stack,
        base.memory, pushedGas + zeroCost + zeroCost + eventCost⟩)
      finishSetPauserPauseSuffix (.error (.revert, raw)) := by
    change Func.RunCompiledTo fs sevm
      (base.setMach ⟨target :: previousPauser :: newPauser :: stack,
        base.memory, pushedGas + zeroCost + zeroCost + eventCost⟩)
      (Ninst.pushB256 pauserSetEvent ::: Ninst.pushB256 zeroWord :::
        Ninst.pushB256 zeroWord ::: (.reg (.log 4)) :::
        finishSetPauserPauseTerminal) (.error (.revert, raw))
    exact heventTail
  have path : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) run := by
    exact heventPath
  exact ⟨raw, run, rawOutput, path⟩

/-- Exact source cost of the three leading memory loads and the corrected
`PauserSet`/pause suffix. -/
private def finishSetPauserPauseCost (pre : Devm) (target : B256) : Nat :=
  let M₁ := (pre.memory.read (newPauserWord * 32).toNat 32).2
  let afterNew := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (previousPauserWord * 32).toNat 32).2
  let afterPrevious := pre.setMach ⟨[], M₂, 0⟩
  let M₃ := (M₂.read (targetWord * 32).toNat 32).2
  let afterTarget := pre.setMach ⟨[], M₃, 0⟩
  finishLoadWordCost pre newPauserWord +
    finishLoadWordCost afterNew previousPauserWord +
    finishLoadWordCost afterPrevious targetWord +
    finishSetPauserPauseSuffixCost afterTarget target

/-- The three source `loadWord`s prepend the corrected event/pause suffix,
without assuming an execution equivalent to the result. -/
private theorem finishSetPauser_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target : B256} {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hgas : pre.gasLeft = G + finishSetPauserPauseCost pre target)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre finishSetPauser
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M₁ := (pre.memory.read (newPauserWord * 32).toNat 32).2
  let afterNew := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (previousPauserWord * 32).toNat 32).2
  let afterPrevious := pre.setMach ⟨[], M₂, 0⟩
  let M₃ := (M₂.read (targetWord * 32).toNat 32).2
  let afterTarget := pre.setMach ⟨[], M₃, 0⟩
  let suffixCost := finishSetPauserPauseSuffixCost afterTarget target
  let targetCost := finishLoadWordCost afterPrevious targetWord
  let previousCost := finishLoadWordCost afterNew previousPauserWord
  let newCost := finishLoadWordCost pre newPauserWord
  have hwf₁ : Mem.Wf M₁ := hwf.extend _ _
  have hr₁ : Mem.Reads M₁ img := Mem.Reads.extend hr _ _
  have hwf₂ : Mem.Wf M₂ := hwf₁.extend _ _
  have hr₂ : Mem.Reads M₂ img := Mem.Reads.extend hr₁ _ _
  have hwf₃ : Mem.Wf M₃ := hwf₂.extend _ _
  have hr₃ : Mem.Reads M₃ img := Mem.Reads.extend hr₂ _ _
  have hnewValue : Bytes.toB256
      (pre.memory.read (newPauserWord * 32).toNat 32).1 = newPauser := by
    rw [Mem.Reads.read hr]
    exact hnewRead
  have haccessSetMach (d : Devm) (s' : List B256)
      (m' : Mem) (g' : Nat) :
      (d.setMach ⟨s', m', g'⟩).accessedAddresses =
        d.accessedAddresses := rfl
  have hpreviousValue : Bytes.toB256
      (M₁.read (previousPauserWord * 32).toNat 32).1 = previousPauser := by
    rw [Mem.Reads.read hr₁]
    exact hpreviousRead
  have htargetValue : Bytes.toB256
      (M₂.read (targetWord * 32).toNat 32).1 = target := by
    rw [Mem.Reads.read hr₂]
    exact htargetRead
  rcases finishSetPauser_pause_suffix_runCompiledTo
      (sevm := sevm) (base := afterTarget) (G := G)
      (by change Mem.Wf M₃; exact hwf₃)
      (by change Mem.Reads M₃ img; exact hr₃)
      htargetRead hcontinuationRead
      (by change (pre.getCode target.toAdr).size = 0; exact hcodeSize)
      (by
        change target.toAdr ∈ pre.accessedAddresses ∨
          target.toAdr ∉ pre.accessedAddresses
        exact haccess)
      hroom hstatic hemptyLookup hpauseLookup with
    ⟨raw, hsuffix, rawOutput, hsuffixPath⟩
  have hsuffix' : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨target :: previousPauser :: newPauser :: stack,
        M₃, G + suffixCost⟩)
      finishSetPauserPauseSuffix (.error (.revert, raw)) := by
    simpa only [suffixCost, afterTarget, Devm.setMach_setMach,
      Devm.memory_setMach] using hsuffix
  have hsuffixPath' : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) hsuffix' := by
    exact hsuffixPath
  have htargetGas :
      (pre.setMach ⟨previousPauser :: newPauser :: stack, M₂,
        G + suffixCost + targetCost⟩).gasLeft =
      (G + suffixCost) + finishLoadWordCost
        (pre.setMach ⟨previousPauser :: newPauser :: stack, M₂,
          G + suffixCost + targetCost⟩) targetWord := by
    dsimp only [targetCost, afterPrevious]
    simp only [Devm.gasLeft_setMach, finishLoadWordCost, Devm.extCost,
      Devm.memory_setMach]
  rcases loadWord_prepend_directPause
      (pre := pre.setMach ⟨previousPauser :: newPauser :: stack, M₂,
        G + suffixCost + targetCost⟩)
      (word := targetWord) (value := target) (markedTarget := target)
      (hstack := rfl) htargetValue htargetGas
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
      hsuffix' hsuffixPath' with
    ⟨htarget, htargetPath⟩
  have hpreviousGas :
      (pre.setMach ⟨newPauser :: stack, M₁,
        G + suffixCost + targetCost + previousCost⟩).gasLeft =
      (G + suffixCost + targetCost) + finishLoadWordCost
        (pre.setMach ⟨newPauser :: stack, M₁,
          G + suffixCost + targetCost + previousCost⟩)
        previousPauserWord := by
    dsimp only [previousCost, afterNew]
    simp only [Devm.gasLeft_setMach, finishLoadWordCost, Devm.extCost,
      Devm.memory_setMach]
  rcases loadWord_prepend_directPause
      (pre := pre.setMach ⟨newPauser :: stack, M₁,
        G + suffixCost + targetCost + previousCost⟩)
      (word := previousPauserWord) (value := previousPauser)
      (markedTarget := target) (hstack := rfl) hpreviousValue hpreviousGas
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
      htarget htargetPath with
    ⟨hprevious, hpreviousPath⟩
  have hnewGas : pre.gasLeft =
      (G + suffixCost + targetCost + previousCost) +
        finishLoadWordCost pre newPauserWord := by
    rw [hgas]
    dsimp only [finishSetPauserPauseCost, suffixCost, targetCost,
      previousCost, newCost, afterTarget, afterPrevious, afterNew,
      M₃, M₂, M₁]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := newPauserWord) (value := newPauser)
      (markedTarget := target) hstack hnewValue hnewGas
      (by omega) hprevious hpreviousPath with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa [finishSetPauser, finishSetPauserPauseSuffix,
      finishSetPauserPauseTerminal] using run,
    rawOutput,
    by simpa [finishSetPauser, finishSetPauserPauseSuffix,
      finishSetPauserPauseTerminal] using path⟩

/-- The common `finishSetPauser` continuation can be entered directly from a
Registry-write suffix, preserving the direct-pause certificate. -/
private theorem finishSetPauser_call_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre finishPre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target : B256} {G : Nat}
    (hstack : finishPre.stack = stack)
    (hwf : Mem.Wf finishPre.memory)
    (hr : Mem.Reads finishPre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hcodeSize : (finishPre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ finishPre.accessedAddresses ∨
      target.toAdr ∉ finishPre.accessedAddresses)
    (hgas : finishPre.gasLeft = G +
      finishSetPauserPauseCost finishPre target)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hcallRoom : pre.stack.length < 1024)
    (hcallBurn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre finishPre) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm
        pre
        (.call finishSetPauserSlot) (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  rcases finishSetPauser_pause_runCompiledTo
      (pre := finishPre) (G := G) hstack hwf hr
      hnewRead hpreviousRead htargetRead hcontinuationRead
      hcodeSize haccess hgas hroom hstatic hemptyLookup hpauseLookup with
    ⟨raw, hfinish, rawOutput, hfinishPath⟩
  let run := Func.RunCompiledTo.call hfinishLookup hcallRoom hcallBurn hfinish
  have path : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) run :=
    .call (lookup := hfinishLookup) (room := hcallRoom)
      (burn := hcallBurn) (tail := hfinish) hfinishPath
  exact ⟨raw, run, rawOutput, path⟩

/-- Reserved source cost for the final reverse-index clear and its
`finishSetPauser` continuation.  Reserving the worst-case warm `SSTORE` cost
lets the construction retain any unused storage gas in the terminal path. -/
private def removeTargetFinalPauseCost (pre : Devm) (target : B256) : Nat :=
  let loaded := pre.setMach ⟨[],
    (pre.memory.read (targetWord * 32).toNat 32).2, 0⟩
  pushCost (0 : B256).toBytes.sig +
    finishLoadWordCost pre targetWord +
    gVerylow + pushCost (regionWord indexRegion).toBytes.sig +
    gasStorageSet + (gVerylow + gMid + gJumpdest) +
    finishSetPauserPauseCost loaded target

/- The final `removeTarget` reverse-index clear enters `finishSetPauser`
directly.  The warm store and internal call are constructed from exact machine
premises; no execution of the suffix is assumed. -/
private theorem removeTarget_final_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target : B256} {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarm : (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
      pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hgas : pre.gasLeft = G + removeTargetFinalPauseCost pre target) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 0 ::: targetIndexKey +++ sstore :::
          .call finishSetPauserSlot) (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M := (pre.memory.read (targetWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M, 0⟩
  let finishCost := finishSetPauserPauseCost loaded target
  let callCost := gVerylow + gMid + gJumpdest
  let zeroPushCost := pushCost (0 : B256).toBytes.sig
  let tagPushCost := pushCost (regionWord indexRegion).toBytes.sig
  let storeGas := G + finishCost + callCost + gasStorageSet
  let tagGas := storeGas + gVerylow + tagPushCost
  let loadGas := tagGas + finishLoadWordCost pre targetWord
  have hwfM : Mem.Wf M := hwf.extend _ _
  have hrM : Mem.Reads M img := Mem.Reads.extend hr _ _
  have htargetValue : Bytes.toB256
      (pre.memory.read (targetWord * 32).toNat 32).1 = target := by
    rw [Mem.Reads.read hr]
    exact htargetRead
  let storePre := pre.setMach
    ⟨indexSlot target :: 0 :: stack, M, storeGas⟩
  have hstoreStack : storePre.stack = indexSlot target :: 0 :: stack := rfl
  have hstoreWarm :
      (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
        storePre.accessedStorageKeys := by
    exact hwarm
  have hstoreMemory : storePre.memory = M := rfl
  have hstoreGas : gasStorageSet ≤ storePre.gasLeft := by
    dsimp only [storePre, storeGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sstore_warm_revert_step
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (devm := storePre)
      (k := indexSlot target) (v := 0) (s := stack) (M := M)
      (rest := .call finishSetPauserSlot)
      hstoreStack hstoreWarm hstatic hstoreMemory hstoreGas (by
        intro base c storeTailGas hkey hother hbalances hcode hkeys
          haddresses hlogs hbound hstoreGasEq
        let spare := gasStorageSet - c
        have htailGas : storeTailGas =
            G + spare + finishCost + callCost := by
          dsimp only [storePre, storeGas] at hstoreGasEq
          simp only [Devm.gasLeft_setMach] at hstoreGasEq
          dsimp only [spare]
          omega
        let callPre := base.setMach ⟨stack, M, storeTailGas⟩
        let finishPre := base.setMach
          ⟨stack, M, G + spare + finishCost⟩
        have hfinishStack : finishPre.stack = stack := rfl
        have hfinishWf : Mem.Wf finishPre.memory := by
          exact hwfM
        have hfinishReads : Mem.Reads finishPre.memory img := by
          exact hrM
        have hfinishCodeSize :
            (finishPre.getCode target.toAdr).size = 0 := by
          change (base.getCode target.toAdr).size = 0
          rw [hcode target.toAdr]
          exact hcodeSize
        have hfinishAccess :
            target.toAdr ∈ finishPre.accessedAddresses ∨
              target.toAdr ∉ finishPre.accessedAddresses := by
          change target.toAdr ∈ base.accessedAddresses ∨
            target.toAdr ∉ base.accessedAddresses
          rw [haddresses]
          exact haccess
        have hfinishCostEq :
            finishSetPauserPauseCost finishPre target = finishCost := by
          dsimp only [finishCost, finishPre, loaded,
            finishSetPauserPauseCost, finishSetPauserPauseSuffixCost,
            finishSetPauserPauseTerminalCost,
            finishSetPauserPauseBranchCost,
            finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
            finishLoadWordCost]
          simp only [Devm.memory_setMach, Devm.extCost]
          congr 10
          congr 1
        have hfinishGas : finishPre.gasLeft =
            (G + spare) + finishSetPauserPauseCost finishPre target := by
          simp only [finishPre, Devm.gasLeft_setMach, hfinishCostEq]
        have hcallRoom : callPre.stack.length < 1024 := by
          simp only [callPre, Devm.stack_setMach]
          omega
        have hcallGas : callPre.gasLeft =
            finishPre.gasLeft + (gVerylow + gMid + gJumpdest) := by
          simp only [callPre, finishPre, Devm.gasLeft_setMach]
          dsimp only [callCost] at htailGas
          omega
        have hcallBurn : Devm.BurnBy
            (gVerylow + gMid + gJumpdest) callPre finishPre := by
          convert Devm.burnBy_setMach_gas
            (devm := callPre) (cost := gVerylow + gMid + gJumpdest)
            (G := finishPre.gasLeft) hcallGas using 1
          all_goals rfl
        rcases finishSetPauser_call_pause_runCompiledTo
            (pre := callPre) (finishPre := finishPre)
            (G := G + spare) hfinishStack hfinishWf hfinishReads
            hnewRead hpreviousRead htargetRead hcontinuationRead
            hfinishCodeSize hfinishAccess hfinishGas hroom hstatic
            hemptyLookup hpauseLookup hfinishLookup hcallRoom hcallBurn with
          ⟨raw, tail, rawOutput, tailPath⟩
        exact ⟨raw, tail, rawOutput, tailPath⟩) with
    ⟨raw, storeRun, rawOutput, storePath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (base := loaded) (region := indexRegion)
      (x := target) (stack := 0 :: stack) (pushGas := tagPushCost)
      (G := storeGas) (hpushCost := rfl)
      (hroom := by simp only [List.length_cons]; omega)
      (by simpa only [storePre, loaded, indexSlot, Devm.setMach_setMach,
          Devm.memory_setMach] using storeRun)
      (by simpa only [storePre, loaded, indexSlot, Devm.setMach_setMach,
          Devm.memory_setMach] using storePath) with
    ⟨tagRun, tagPath⟩
  have hloadGas :
      (pre.setMach ⟨0 :: stack, pre.memory, loadGas⟩).gasLeft =
        tagGas + finishLoadWordCost
          (pre.setMach ⟨0 :: stack, pre.memory, loadGas⟩) targetWord := by
    change loadGas = tagGas + finishLoadWordCost pre targetWord
    dsimp only [loadGas]
  rcases loadWord_prepend_directPause
      (pre := pre.setMach ⟨0 :: stack, pre.memory, loadGas⟩)
      (word := targetWord) (value := target) (markedTarget := target)
      (G := tagGas) (hstack := rfl) htargetValue hloadGas
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
      (by simpa only [M, loaded, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach]
        using tagRun)
      (by simpa only [M, loaded, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach]
        using tagPath) with
    ⟨loadRun, loadPath⟩
  have hstartGas : pre.gasLeft = loadGas + zeroPushCost := by
    rw [hgas]
    dsimp only [removeTargetFinalPauseCost, loaded, M, finishCost,
      callCost, zeroPushCost, tagPushCost, storeGas, tagGas, loadGas]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target) (word := 0)
      (phase := .beforeZeroCode) (pre := pre) (stack := stack)
      (c := zeroPushCost) (G := loadGas) hstack rfl hstartGas
      (by omega) loadRun loadPath with
    ⟨run, path⟩
  exact ⟨raw, by simpa only [targetIndexKey, prepend_append] using run,
    rawOutput,
    by simpa only [targetIndexKey, prepend_append] using path⟩

/-- Reserved source cost for the array-length decrement write followed by the
final reverse-index clear. -/
private def removeTargetLengthPauseCost (pre : Devm) (target : B256) : Nat :=
  let loaded := pre.setMach ⟨[],
    (pre.memory.read (arrayLengthWord * 32).toNat 32).2, 0⟩
  finishLoadWordCost pre arrayLengthWord +
    pushCost (1 : B256).toBytes.sig + gVerylow + gVerylow +
    pushCost arrayLengthSlot.toBytes.sig + gasStorageSet +
    removeTargetFinalPauseCost loaded target

/- The array-length decrement is the immediately preceding `removeTarget`
write.  Its arithmetic and warm store are constructed directly, then the
already-proved final reverse-index suffix is used as the continuation. -/
private theorem removeTarget_length_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target arrayLength decrementedLength : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (harrayLengthRead : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmLength :
      (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmIndex :
      (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hgas : pre.gasLeft = G + removeTargetLengthPauseCost pre target) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
          pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
          targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M := (pre.memory.read (arrayLengthWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M, 0⟩
  let suffixCost := removeTargetFinalPauseCost loaded target
  let slotPushCost := pushCost arrayLengthSlot.toBytes.sig
  let onePushCost := pushCost (1 : B256).toBytes.sig
  let storeGas := G + suffixCost + gasStorageSet
  let slotPushGas := storeGas + slotPushCost
  let subGas := slotPushGas + gVerylow
  let swapGas := subGas + gVerylow
  let onePushGas := swapGas + onePushCost
  let loadGas := onePushGas + finishLoadWordCost pre arrayLengthWord
  have hwfM : Mem.Wf M := hwf.extend _ _
  have hrM : Mem.Reads M img := Mem.Reads.extend hr _ _
  have hlengthValue : Bytes.toB256
      (pre.memory.read (arrayLengthWord * 32).toNat 32).1 = arrayLength := by
    rw [Mem.Reads.read hr]
    exact harrayLengthRead
  let storePre := pre.setMach
    ⟨arrayLengthSlot :: decrementedLength :: stack, M, storeGas⟩
  have hstoreStack :
      storePre.stack = arrayLengthSlot :: decrementedLength :: stack := rfl
  have hstoreWarm :
      (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
        storePre.accessedStorageKeys := by
    exact hwarmLength
  have hstoreMemory : storePre.memory = M := rfl
  have hstoreGas : gasStorageSet ≤ storePre.gasLeft := by
    dsimp only [storePre, storeGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sstore_warm_revert_step
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (devm := storePre)
      (k := arrayLengthSlot) (v := decrementedLength)
      (s := stack) (M := M)
      (rest := pushB256 0 ::: targetIndexKey +++ sstore :::
        .call finishSetPauserSlot)
      hstoreStack hstoreWarm hstatic hstoreMemory hstoreGas (by
        intro base c storeTailGas hkey hother hbalances hcode hkeys
          haddresses hlogs hbound hstoreGasEq
        let spare := gasStorageSet - c
        have htailGas : storeTailGas = G + spare + suffixCost := by
          dsimp only [storePre, storeGas] at hstoreGasEq
          simp only [Devm.gasLeft_setMach] at hstoreGasEq
          dsimp only [spare]
          omega
        let suffixPre := base.setMach ⟨stack, M, storeTailGas⟩
        have hsuffixStack : suffixPre.stack = stack := rfl
        have hsuffixWf : Mem.Wf suffixPre.memory := hwfM
        have hsuffixReads : Mem.Reads suffixPre.memory img := hrM
        have hsuffixCodeSize :
            (suffixPre.getCode target.toAdr).size = 0 := by
          change (base.getCode target.toAdr).size = 0
          rw [hcode target.toAdr]
          exact hcodeSize
        have hsuffixAccess :
            target.toAdr ∈ suffixPre.accessedAddresses ∨
              target.toAdr ∉ suffixPre.accessedAddresses := by
          change target.toAdr ∈ base.accessedAddresses ∨
            target.toAdr ∉ base.accessedAddresses
          rw [haddresses]
          exact haccess
        have hsuffixWarm :
            (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, indexSlot target⟩ :
            Adr × B256) ∈ base.accessedStorageKeys
          rw [hkeys]
          exact hwarmIndex
        have haccessSetMach (d : Devm) (s' : List B256)
            (m' : Mem) (g' : Nat) :
            (d.setMach ⟨s', m', g'⟩).accessedAddresses =
              d.accessedAddresses := rfl
        have hbaseAddresses :
            base.accessedAddresses = pre.accessedAddresses := by
          change base.accessedAddresses = pre.accessedAddresses at haddresses
          exact haddresses
        have hsuffixCostEq :
            removeTargetFinalPauseCost suffixPre target = suffixCost := by
          dsimp only [suffixCost, suffixPre, loaded,
            removeTargetFinalPauseCost, finishSetPauserPauseCost,
            finishSetPauserPauseSuffixCost,
            finishSetPauserPauseTerminalCost,
            finishSetPauserPauseBranchCost,
            finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
            finishLoadWordCost]
          simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
          rw [hbaseAddresses]
        have hsuffixGas : suffixPre.gasLeft =
            (G + spare) + removeTargetFinalPauseCost suffixPre target := by
          simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
          omega
        rcases removeTarget_final_pause_suffix_runCompiledTo
            (pre := suffixPre) (G := G + spare) hsuffixStack hsuffixWf
            hsuffixReads hnewRead hpreviousRead htargetRead
            hcontinuationRead hsuffixCodeSize hsuffixAccess hsuffixWarm
            hroom hstatic hemptyLookup hpauseLookup hfinishLookup
            hsuffixGas with
          ⟨raw, tail, rawOutput, tailPath⟩
        exact ⟨raw, tail, rawOutput, tailPath⟩) with
    ⟨raw, storeRun, rawOutput, storePath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (word := arrayLengthSlot) (phase := .beforeZeroCode)
      (pre := loaded.setMach
        ⟨decrementedLength :: stack, M, slotPushGas⟩)
      (stack := decrementedLength :: stack) (c := slotPushCost)
      (G := storeGas) rfl rfl rfl
      (by simp only [List.length_cons]; omega)
      (by simpa only [storePre, loaded, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using storeRun)
      (by simpa only [storePre, loaded, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using storePath) with
    ⟨slotRun, slotPath⟩
  have hsub : Ninst.RunCompiled sevm
      (loaded.setMach ⟨arrayLength :: 1 :: stack, M, subGas⟩) sub
      (loaded.setMach ⟨decrementedLength :: stack, M, slotPushGas⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Ninst.runCompiled_binary
        (sevm := sevm)
        (devm := loaded.setMach
          ⟨arrayLength :: 1 :: stack, M, subGas⟩)
        (r := .sub) (f := (· - ·)) (cost := gVerylow)
        (x := arrayLength) (y := 1) (v := decrementedLength)
        (s := stack) (G := slotPushGas) (by rintro ⟨⟩) rfl rfl
        hdecrement (by
          simp only [Devm.gasLeft_setMach]
          dsimp only [subGas]) (by omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hsub (by simp)
      slotRun slotPath with ⟨subRun, subPath⟩
  have hswap : Ninst.RunCompiled sevm
      (loaded.setMach ⟨1 :: arrayLength :: stack, M, swapGas⟩) (swap 0)
      (loaded.setMach ⟨arrayLength :: 1 :: stack, M, subGas⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Ninst.runCompiled_swap
        (sevm := sevm)
        (devm := loaded.setMach
          ⟨1 :: arrayLength :: stack, M, swapGas⟩)
        (n := 0) (S := arrayLength :: 1 :: stack) (G := subGas) rfl
        (by
          simp only [Devm.gasLeft_setMach]
          dsimp only [swapGas])
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hswap (by simp)
      subRun subPath with ⟨swapRun, swapPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target) (word := 1)
      (phase := .beforeZeroCode)
      (pre := loaded.setMach
        ⟨arrayLength :: stack, M, onePushGas⟩)
      (stack := arrayLength :: stack) (c := onePushCost)
      (G := swapGas) rfl rfl rfl
      (by simp only [List.length_cons]; omega)
      (by simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using swapRun)
      (by simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using swapPath) with
    ⟨oneRun, onePath⟩
  have hloadGas : pre.gasLeft =
      onePushGas + finishLoadWordCost pre arrayLengthWord := by
    rw [hgas]
    dsimp only [removeTargetLengthPauseCost, loaded, M, suffixCost,
      slotPushCost, onePushCost, storeGas, slotPushGas, subGas,
      swapGas, onePushGas, loadGas]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := arrayLengthWord) (value := arrayLength)
      (markedTarget := target) (G := onePushGas) hstack hlengthValue
      hloadGas (by omega)
      (by simpa only [M, loaded, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using oneRun)
      (by simpa only [M, loaded, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using onePath) with
    ⟨run, path⟩
  exact ⟨raw, run, rawOutput, path⟩

/-- Reserved source cost for clearing the old array tail before the length
decrement and final reverse-index clear. -/
private def removeTargetTailClearPauseCost
    (pre : Devm) (target : B256) : Nat :=
  let loaded := pre.setMach ⟨[],
    (pre.memory.read (arrayLengthWord * 32).toNat 32).2, 0⟩
  pushCost (0 : B256).toBytes.sig +
    finishLoadWordCost pre arrayLengthWord +
    gVerylow + pushCost (regionWord arrayRegion).toBytes.sig +
    gasStorageSet + removeTargetLengthPauseCost loaded target

/- Clear exactly the saved old tail entry, then continue with the proved
array-length decrement suffix. -/
private theorem removeTarget_tail_clear_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target arrayLength decrementedLength : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (harrayLengthRead : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmTail :
      (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmLength :
      (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmIndex :
      (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hgas : pre.gasLeft = G +
      removeTargetTailClearPauseCost pre target) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
          sstore ::: loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 :::
          sub ::: pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
          targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M := (pre.memory.read (arrayLengthWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M, 0⟩
  let suffixCost := removeTargetLengthPauseCost loaded target
  let zeroPushCost := pushCost (0 : B256).toBytes.sig
  let tagPushCost := pushCost (regionWord arrayRegion).toBytes.sig
  let storeGas := G + suffixCost + gasStorageSet
  let tagGas := storeGas + gVerylow + tagPushCost
  let loadGas := tagGas + finishLoadWordCost pre arrayLengthWord
  have hwfM : Mem.Wf M := hwf.extend _ _
  have hrM : Mem.Reads M img := Mem.Reads.extend hr _ _
  have hlengthValue : Bytes.toB256
      (pre.memory.read (arrayLengthWord * 32).toNat 32).1 = arrayLength := by
    rw [Mem.Reads.read hr]
    exact harrayLengthRead
  let storePre := pre.setMach
    ⟨arrayEntrySlot arrayLength :: 0 :: stack, M, storeGas⟩
  have hstoreStack :
      storePre.stack = arrayEntrySlot arrayLength :: 0 :: stack := rfl
  have hstoreWarm :
      (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ : Adr × B256) ∈
        storePre.accessedStorageKeys := by
    exact hwarmTail
  have hstoreMemory : storePre.memory = M := rfl
  have hstoreGas : gasStorageSet ≤ storePre.gasLeft := by
    dsimp only [storePre, storeGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sstore_warm_revert_step
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (devm := storePre)
      (k := arrayEntrySlot arrayLength) (v := 0) (s := stack) (M := M)
      (rest := loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 :::
        sub ::: pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
        targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
      hstoreStack hstoreWarm hstatic hstoreMemory hstoreGas (by
        intro base c storeTailGas hkey hother hbalances hcode hkeys
          haddresses hlogs hbound hstoreGasEq
        let spare := gasStorageSet - c
        have htailGas : storeTailGas = G + spare + suffixCost := by
          dsimp only [storePre, storeGas] at hstoreGasEq
          simp only [Devm.gasLeft_setMach] at hstoreGasEq
          dsimp only [spare]
          omega
        let suffixPre := base.setMach ⟨stack, M, storeTailGas⟩
        have hsuffixStack : suffixPre.stack = stack := rfl
        have hsuffixWf : Mem.Wf suffixPre.memory := hwfM
        have hsuffixReads : Mem.Reads suffixPre.memory img := hrM
        have hsuffixCodeSize :
            (suffixPre.getCode target.toAdr).size = 0 := by
          change (base.getCode target.toAdr).size = 0
          rw [hcode target.toAdr]
          exact hcodeSize
        have hsuffixAccess :
            target.toAdr ∈ suffixPre.accessedAddresses ∨
              target.toAdr ∉ suffixPre.accessedAddresses := by
          change target.toAdr ∈ base.accessedAddresses ∨
            target.toAdr ∉ base.accessedAddresses
          rw [haddresses]
          exact haccess
        have hsuffixWarmLength :
            (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
            base.accessedStorageKeys
          rw [hkeys]
          exact hwarmLength
        have hsuffixWarmIndex :
            (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, indexSlot target⟩ :
            Adr × B256) ∈ base.accessedStorageKeys
          rw [hkeys]
          exact hwarmIndex
        have haccessSetMach (d : Devm) (s' : List B256)
            (m' : Mem) (g' : Nat) :
            (d.setMach ⟨s', m', g'⟩).accessedAddresses =
              d.accessedAddresses := rfl
        have hbaseAddresses :
            base.accessedAddresses = pre.accessedAddresses := by
          change base.accessedAddresses = pre.accessedAddresses at haddresses
          exact haddresses
        have hsuffixCostEq :
            removeTargetLengthPauseCost suffixPre target = suffixCost := by
          dsimp only [suffixCost, suffixPre, loaded,
            removeTargetLengthPauseCost, removeTargetFinalPauseCost,
            finishSetPauserPauseCost, finishSetPauserPauseSuffixCost,
            finishSetPauserPauseTerminalCost,
            finishSetPauserPauseBranchCost,
            finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
            finishLoadWordCost]
          simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
          rw [hbaseAddresses]
        have hsuffixGas : suffixPre.gasLeft =
            (G + spare) + removeTargetLengthPauseCost suffixPre target := by
          simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
          omega
        rcases removeTarget_length_pause_suffix_runCompiledTo
            (pre := suffixPre) (G := G + spare) hsuffixStack hsuffixWf
            hsuffixReads hnewRead hpreviousRead htargetRead
            hcontinuationRead harrayLengthRead hdecrement hsuffixCodeSize
            hsuffixAccess hsuffixWarmLength hsuffixWarmIndex hroom hstatic
            hemptyLookup hpauseLookup hfinishLookup hsuffixGas with
          ⟨raw, tail, rawOutput, tailPath⟩
        exact ⟨raw, tail, rawOutput, tailPath⟩) with
    ⟨raw, storeRun, rawOutput, storePath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (base := loaded) (region := arrayRegion)
      (x := arrayLength) (stack := 0 :: stack) (pushGas := tagPushCost)
      (G := storeGas) (hpushCost := rfl)
      (hroom := by simp only [List.length_cons]; omega)
      (by simpa only [storePre, loaded, arrayEntrySlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using storeRun)
      (by simpa only [storePre, loaded, arrayEntrySlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using storePath) with
    ⟨tagRun, tagPath⟩
  have hloadGas :
      (pre.setMach ⟨0 :: stack, pre.memory, loadGas⟩).gasLeft =
        tagGas + finishLoadWordCost
          (pre.setMach ⟨0 :: stack, pre.memory, loadGas⟩)
          arrayLengthWord := by
    change loadGas = tagGas + finishLoadWordCost pre arrayLengthWord
    dsimp only [loadGas]
  rcases loadWord_prepend_directPause
      (pre := pre.setMach ⟨0 :: stack, pre.memory, loadGas⟩)
      (word := arrayLengthWord) (value := arrayLength)
      (markedTarget := target) (G := tagGas) (hstack := rfl)
      hlengthValue hloadGas
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
      (by simpa only [M, loaded, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [M, loaded, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨loadRun, loadPath⟩
  have hstartGas : pre.gasLeft = loadGas + zeroPushCost := by
    rw [hgas]
    dsimp only [removeTargetTailClearPauseCost, loaded, M, suffixCost,
      zeroPushCost, tagPushCost, storeGas, tagGas, loadGas]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target) (word := 0)
      (phase := .beforeZeroCode) (pre := pre) (stack := stack)
      (c := zeroPushCost) (G := loadGas) hstack rfl hstartGas
      (by omega) loadRun loadPath with ⟨run, path⟩
  exact ⟨raw, run, rawOutput, path⟩

/-- Reserved source cost for repairing the moved target's reverse index before
the proved tail-clear suffix. -/
private def removeTargetMovedIndexPauseCost
    (pre : Devm) (target : B256) : Nat :=
  let M₁ := (pre.memory.read (removedIndexWord * 32).toNat 32).2
  let afterRemoved := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (lastTargetWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  finishLoadWordCost pre removedIndexWord +
    finishLoadWordCost afterRemoved lastTargetWord +
    gVerylow + pushCost (regionWord indexRegion).toBytes.sig +
    gasStorageSet + removeTargetTailClearPauseCost loaded target

/- Repair exactly the saved last target's reverse index, then continue with
the proved old-tail clear. -/
private theorem removeTarget_moved_index_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target arrayLength decrementedLength
      removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (harrayLengthRead : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = arrayLength)
    (hremovedIndexRead : Bytes.toB256
      (img.sliceD (removedIndexWord * 32).toNat 32 0) = removedIndex)
    (hlastTargetRead : Bytes.toB256
      (img.sliceD (lastTargetWord * 32).toNat 32 0) = lastTarget)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (_hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmTail :
      (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmLength :
      (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmIndex :
      (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hgas : pre.gasLeft = G +
      removeTargetMovedIndexPauseCost pre target) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (loadWord removedIndexWord +++ lastTargetIndexKey +++ sstore :::
          pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
          sstore ::: loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 :::
          sub ::: pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
          targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M₁ := (pre.memory.read (removedIndexWord * 32).toNat 32).2
  let afterRemoved := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (lastTargetWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  let suffixCost := removeTargetTailClearPauseCost loaded target
  let tagPushCost := pushCost (regionWord indexRegion).toBytes.sig
  let storeGas := G + suffixCost + gasStorageSet
  let tagGas := storeGas + gVerylow + tagPushCost
  let lastLoadGas :=
    tagGas + finishLoadWordCost afterRemoved lastTargetWord
  let removedLoadGas :=
    lastLoadGas + finishLoadWordCost pre removedIndexWord
  have hwf₁ : Mem.Wf M₁ := hwf.extend _ _
  have hr₁ : Mem.Reads M₁ img := Mem.Reads.extend hr _ _
  have hwf₂ : Mem.Wf M₂ := hwf₁.extend _ _
  have hr₂ : Mem.Reads M₂ img := Mem.Reads.extend hr₁ _ _
  have hremovedValue : Bytes.toB256
      (pre.memory.read (removedIndexWord * 32).toNat 32).1 =
        removedIndex := by
    rw [Mem.Reads.read hr]
    exact hremovedIndexRead
  have hlastValue : Bytes.toB256
      (M₁.read (lastTargetWord * 32).toNat 32).1 = lastTarget := by
    rw [Mem.Reads.read hr₁]
    exact hlastTargetRead
  let storePre := pre.setMach
    ⟨indexSlot lastTarget :: removedIndex :: stack, M₂, storeGas⟩
  have hstoreStack :
      storePre.stack = indexSlot lastTarget :: removedIndex :: stack := rfl
  have hstoreWarm :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        storePre.accessedStorageKeys := by
    exact hwarmMovedIndex
  have hstoreMemory : storePre.memory = M₂ := rfl
  have hstoreGas : gasStorageSet ≤ storePre.gasLeft := by
    dsimp only [storePre, storeGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sstore_warm_revert_step
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (devm := storePre)
      (k := indexSlot lastTarget) (v := removedIndex)
      (s := stack) (M := M₂)
      (rest := pushB256 0 ::: loadWord arrayLengthWord +++
        tagTop arrayRegion +++ sstore ::: loadWord arrayLengthWord +++
        pushB256 1 ::: swap 0 ::: sub ::: pushB256 arrayLengthSlot :::
        sstore ::: pushB256 0 ::: targetIndexKey +++ sstore :::
        .call finishSetPauserSlot)
      hstoreStack hstoreWarm hstatic hstoreMemory hstoreGas (by
        intro base c storeTailGas hkey hother hbalances hcode hkeys
          haddresses hlogs hbound hstoreGasEq
        let spare := gasStorageSet - c
        have htailGas : storeTailGas = G + spare + suffixCost := by
          dsimp only [storePre, storeGas] at hstoreGasEq
          simp only [Devm.gasLeft_setMach] at hstoreGasEq
          dsimp only [spare]
          omega
        let suffixPre := base.setMach ⟨stack, M₂, storeTailGas⟩
        have hsuffixStack : suffixPre.stack = stack := rfl
        have hsuffixWf : Mem.Wf suffixPre.memory := hwf₂
        have hsuffixReads : Mem.Reads suffixPre.memory img := hr₂
        have hsuffixCodeSize :
            (suffixPre.getCode target.toAdr).size = 0 := by
          change (base.getCode target.toAdr).size = 0
          rw [hcode target.toAdr]
          exact hcodeSize
        have hsuffixAccess :
            target.toAdr ∈ suffixPre.accessedAddresses ∨
              target.toAdr ∉ suffixPre.accessedAddresses := by
          change target.toAdr ∈ base.accessedAddresses ∨
            target.toAdr ∉ base.accessedAddresses
          rw [haddresses]
          exact haccess
        have hsuffixWarmTail :
            (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ :
              Adr × B256) ∈ suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ :
            Adr × B256) ∈ base.accessedStorageKeys
          rw [hkeys]
          exact hwarmTail
        have hsuffixWarmLength :
            (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
            base.accessedStorageKeys
          rw [hkeys]
          exact hwarmLength
        have hsuffixWarmIndex :
            (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, indexSlot target⟩ :
            Adr × B256) ∈ base.accessedStorageKeys
          rw [hkeys]
          exact hwarmIndex
        have haccessSetMach (d : Devm) (s' : List B256)
            (m' : Mem) (g' : Nat) :
            (d.setMach ⟨s', m', g'⟩).accessedAddresses =
              d.accessedAddresses := rfl
        have hbaseAddresses :
            base.accessedAddresses = pre.accessedAddresses := by
          change base.accessedAddresses = pre.accessedAddresses at haddresses
          exact haddresses
        have hsuffixCostEq :
            removeTargetTailClearPauseCost suffixPre target = suffixCost := by
          dsimp only [suffixCost, suffixPre, loaded,
            removeTargetTailClearPauseCost, removeTargetLengthPauseCost,
            removeTargetFinalPauseCost, finishSetPauserPauseCost,
            finishSetPauserPauseSuffixCost,
            finishSetPauserPauseTerminalCost,
            finishSetPauserPauseBranchCost,
            finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
            finishLoadWordCost]
          simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
          rw [hbaseAddresses]
        have hsuffixGas : suffixPre.gasLeft =
            (G + spare) + removeTargetTailClearPauseCost suffixPre target := by
          simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
          omega
        rcases removeTarget_tail_clear_pause_suffix_runCompiledTo
            (pre := suffixPre) (G := G + spare) hsuffixStack hsuffixWf
            hsuffixReads hnewRead hpreviousRead htargetRead
            hcontinuationRead harrayLengthRead hdecrement hsuffixCodeSize
            hsuffixAccess hsuffixWarmTail hsuffixWarmLength hsuffixWarmIndex
            hroom hstatic hemptyLookup hpauseLookup hfinishLookup
            hsuffixGas with ⟨raw, tail, rawOutput, tailPath⟩
        exact ⟨raw, tail, rawOutput, tailPath⟩) with
    ⟨raw, storeRun, rawOutput, storePath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (base := loaded) (region := indexRegion)
      (x := lastTarget) (stack := removedIndex :: stack)
      (pushGas := tagPushCost) (G := storeGas) (hpushCost := rfl)
      (hroom := by simp only [List.length_cons]; omega)
      (by simpa only [storePre, loaded, indexSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using storeRun)
      (by simpa only [storePre, loaded, indexSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using storePath) with
    ⟨tagRun, tagPath⟩
  have hlastLoadGas :
      (afterRemoved.setMach
        ⟨removedIndex :: stack, M₁, lastLoadGas⟩).gasLeft =
        tagGas + finishLoadWordCost
          (afterRemoved.setMach
            ⟨removedIndex :: stack, M₁, lastLoadGas⟩)
          lastTargetWord := by
    change lastLoadGas =
      tagGas + finishLoadWordCost afterRemoved lastTargetWord
    dsimp only [lastLoadGas]
  rcases loadWord_prepend_directPause
      (pre := afterRemoved.setMach
        ⟨removedIndex :: stack, M₁, lastLoadGas⟩)
      (word := lastTargetWord) (value := lastTarget)
      (markedTarget := target) (G := tagGas) (hstack := rfl)
      hlastValue hlastLoadGas
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
      (by simpa only [M₂, loaded, afterRemoved, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [M₂, loaded, afterRemoved, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨lastRun, lastPath⟩
  have hremovedLoadGas : pre.gasLeft =
      lastLoadGas + finishLoadWordCost pre removedIndexWord := by
    rw [hgas]
    dsimp only [removeTargetMovedIndexPauseCost, afterRemoved, loaded,
      M₁, M₂, suffixCost, tagPushCost, storeGas, tagGas,
      lastLoadGas, removedLoadGas]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := removedIndexWord) (value := removedIndex)
      (markedTarget := target) (G := lastLoadGas) hstack hremovedValue
      hremovedLoadGas (by omega)
      (by simpa only [M₁, afterRemoved, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using lastRun)
      (by simpa only [M₁, afterRemoved, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using lastPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [lastTargetIndexKey, prepend_append] using run,
    rawOutput,
    by simpa only [lastTargetIndexKey, prepend_append] using path⟩

/-- Reserved source cost for overwriting the removed array hole before the
reverse-index repair suffix. -/
private def removeTargetHolePauseCost
    (pre : Devm) (target : B256) : Nat :=
  let M₁ := (pre.memory.read (lastTargetWord * 32).toNat 32).2
  let afterLast := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (removedIndexWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  finishLoadWordCost pre lastTargetWord +
    finishLoadWordCost afterLast removedIndexWord +
    gVerylow + pushCost (regionWord arrayRegion).toBytes.sig +
    gasStorageSet + removeTargetMovedIndexPauseCost loaded target

/- Overwrite exactly the saved removed slot with the saved last target, then
continue with the proved reverse-index repair. -/
private theorem removeTarget_hole_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target arrayLength decrementedLength
      removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (harrayLengthRead : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = arrayLength)
    (hremovedIndexRead : Bytes.toB256
      (img.sliceD (removedIndexWord * 32).toNat 32 0) = removedIndex)
    (hlastTargetRead : Bytes.toB256
      (img.sliceD (lastTargetWord * 32).toNat 32 0) = lastTarget)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmTail :
      (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmLength :
      (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmIndex :
      (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hgas : pre.gasLeft = G + removeTargetHolePauseCost pre target) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (loadWord lastTargetWord +++ loadWord removedIndexWord +++
          tagTop arrayRegion +++ sstore ::: loadWord removedIndexWord +++
          lastTargetIndexKey +++ sstore ::: pushB256 0 :::
          loadWord arrayLengthWord +++ tagTop arrayRegion +++ sstore :::
          loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
          pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
          targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M₁ := (pre.memory.read (lastTargetWord * 32).toNat 32).2
  let afterLast := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (removedIndexWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  let suffixCost := removeTargetMovedIndexPauseCost loaded target
  let tagPushCost := pushCost (regionWord arrayRegion).toBytes.sig
  let storeGas := G + suffixCost + gasStorageSet
  let tagGas := storeGas + gVerylow + tagPushCost
  let removedLoadGas :=
    tagGas + finishLoadWordCost afterLast removedIndexWord
  let lastLoadGas :=
    removedLoadGas + finishLoadWordCost pre lastTargetWord
  have hwf₁ : Mem.Wf M₁ := hwf.extend _ _
  have hr₁ : Mem.Reads M₁ img := Mem.Reads.extend hr _ _
  have hwf₂ : Mem.Wf M₂ := hwf₁.extend _ _
  have hr₂ : Mem.Reads M₂ img := Mem.Reads.extend hr₁ _ _
  have hlastValue : Bytes.toB256
      (pre.memory.read (lastTargetWord * 32).toNat 32).1 = lastTarget := by
    rw [Mem.Reads.read hr]
    exact hlastTargetRead
  have hremovedValue : Bytes.toB256
      (M₁.read (removedIndexWord * 32).toNat 32).1 = removedIndex := by
    rw [Mem.Reads.read hr₁]
    exact hremovedIndexRead
  let storePre := pre.setMach
    ⟨arrayEntrySlot removedIndex :: lastTarget :: stack, M₂, storeGas⟩
  have hstoreStack :
      storePre.stack = arrayEntrySlot removedIndex :: lastTarget :: stack := rfl
  have hstoreWarm :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        storePre.accessedStorageKeys := by
    exact hwarmHole
  have hstoreMemory : storePre.memory = M₂ := rfl
  have hstoreGas : gasStorageSet ≤ storePre.gasLeft := by
    dsimp only [storePre, storeGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sstore_warm_revert_step
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (devm := storePre)
      (k := arrayEntrySlot removedIndex) (v := lastTarget)
      (s := stack) (M := M₂)
      (rest := loadWord removedIndexWord +++ lastTargetIndexKey +++
        sstore ::: pushB256 0 ::: loadWord arrayLengthWord +++
        tagTop arrayRegion +++ sstore ::: loadWord arrayLengthWord +++
        pushB256 1 ::: swap 0 ::: sub ::: pushB256 arrayLengthSlot :::
        sstore ::: pushB256 0 ::: targetIndexKey +++ sstore :::
        .call finishSetPauserSlot)
      hstoreStack hstoreWarm hstatic hstoreMemory hstoreGas (by
        intro base c storeTailGas hkey hother hbalances hcode hkeys
          haddresses hlogs hbound hstoreGasEq
        let spare := gasStorageSet - c
        have htailGas : storeTailGas = G + spare + suffixCost := by
          dsimp only [storePre, storeGas] at hstoreGasEq
          simp only [Devm.gasLeft_setMach] at hstoreGasEq
          dsimp only [spare]
          omega
        let suffixPre := base.setMach ⟨stack, M₂, storeTailGas⟩
        have hsuffixStack : suffixPre.stack = stack := rfl
        have hsuffixWf : Mem.Wf suffixPre.memory := hwf₂
        have hsuffixReads : Mem.Reads suffixPre.memory img := hr₂
        have hsuffixCodeSize :
            (suffixPre.getCode target.toAdr).size = 0 := by
          change (base.getCode target.toAdr).size = 0
          rw [hcode target.toAdr]
          exact hcodeSize
        have hsuffixAccess :
            target.toAdr ∈ suffixPre.accessedAddresses ∨
              target.toAdr ∉ suffixPre.accessedAddresses := by
          change target.toAdr ∈ base.accessedAddresses ∨
            target.toAdr ∉ base.accessedAddresses
          rw [haddresses]
          exact haccess
        have hsuffixWarmMovedIndex :
            (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, indexSlot lastTarget⟩ :
            Adr × B256) ∈ base.accessedStorageKeys
          rw [hkeys]
          exact hwarmMovedIndex
        have hsuffixWarmTail :
            (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ :
              Adr × B256) ∈ suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ :
            Adr × B256) ∈ base.accessedStorageKeys
          rw [hkeys]
          exact hwarmTail
        have hsuffixWarmLength :
            (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
            base.accessedStorageKeys
          rw [hkeys]
          exact hwarmLength
        have hsuffixWarmIndex :
            (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, indexSlot target⟩ :
            Adr × B256) ∈ base.accessedStorageKeys
          rw [hkeys]
          exact hwarmIndex
        have haccessSetMach (d : Devm) (s' : List B256)
            (m' : Mem) (g' : Nat) :
            (d.setMach ⟨s', m', g'⟩).accessedAddresses =
              d.accessedAddresses := rfl
        have hbaseAddresses :
            base.accessedAddresses = pre.accessedAddresses := by
          change base.accessedAddresses = pre.accessedAddresses at haddresses
          exact haddresses
        have hsuffixCostEq :
            removeTargetMovedIndexPauseCost suffixPre target = suffixCost := by
          dsimp only [suffixCost, suffixPre, loaded,
            removeTargetMovedIndexPauseCost,
            removeTargetTailClearPauseCost, removeTargetLengthPauseCost,
            removeTargetFinalPauseCost, finishSetPauserPauseCost,
            finishSetPauserPauseSuffixCost,
            finishSetPauserPauseTerminalCost,
            finishSetPauserPauseBranchCost,
            finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
            finishLoadWordCost]
          simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
          rw [hbaseAddresses]
        have hsuffixGas : suffixPre.gasLeft =
            (G + spare) + removeTargetMovedIndexPauseCost suffixPre target := by
          simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
          omega
        rcases removeTarget_moved_index_pause_suffix_runCompiledTo
            (pre := suffixPre) (G := G + spare) hsuffixStack hsuffixWf
            hsuffixReads hnewRead hpreviousRead htargetRead
            hcontinuationRead harrayLengthRead hremovedIndexRead
            hlastTargetRead hdecrement hlastCanonical hsuffixCodeSize
            hsuffixAccess hsuffixWarmMovedIndex hsuffixWarmTail
            hsuffixWarmLength hsuffixWarmIndex hroom hstatic hemptyLookup
            hpauseLookup hfinishLookup hsuffixGas with
          ⟨raw, tail, rawOutput, tailPath⟩
        exact ⟨raw, tail, rawOutput, tailPath⟩) with
    ⟨raw, storeRun, rawOutput, storePath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (base := loaded) (region := arrayRegion)
      (x := removedIndex) (stack := lastTarget :: stack)
      (pushGas := tagPushCost) (G := storeGas) (hpushCost := rfl)
      (hroom := by simp only [List.length_cons]; omega)
      (by simpa only [storePre, loaded, arrayEntrySlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using storeRun)
      (by simpa only [storePre, loaded, arrayEntrySlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using storePath) with
    ⟨tagRun, tagPath⟩
  have hremovedLoadGas :
      (afterLast.setMach
        ⟨lastTarget :: stack, M₁, removedLoadGas⟩).gasLeft =
        tagGas + finishLoadWordCost
          (afterLast.setMach
            ⟨lastTarget :: stack, M₁, removedLoadGas⟩)
          removedIndexWord := by
    change removedLoadGas =
      tagGas + finishLoadWordCost afterLast removedIndexWord
    dsimp only [removedLoadGas]
  rcases loadWord_prepend_directPause
      (pre := afterLast.setMach
        ⟨lastTarget :: stack, M₁, removedLoadGas⟩)
      (word := removedIndexWord) (value := removedIndex)
      (markedTarget := target) (G := tagGas) (hstack := rfl)
      hremovedValue hremovedLoadGas
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
      (by simpa only [M₂, loaded, afterLast, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [M₂, loaded, afterLast, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨removedRun, removedPath⟩
  have hlastLoadGas : pre.gasLeft =
      removedLoadGas + finishLoadWordCost pre lastTargetWord := by
    rw [hgas]
    dsimp only [removeTargetHolePauseCost, afterLast, loaded,
      M₁, M₂, suffixCost, tagPushCost, storeGas, tagGas,
      removedLoadGas, lastLoadGas]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := lastTargetWord) (value := lastTarget)
      (markedTarget := target) (G := removedLoadGas) hstack hlastValue
      hlastLoadGas (by omega)
      (by simpa only [M₁, afterLast, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using removedRun)
      (by simpa only [M₁, afterLast, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using removedPath) with
    ⟨run, path⟩
  exact ⟨raw, run, rawOutput, path⟩

/-- Reserved source cost for reading the last array target and saving it in the
removal scratch image before the already-constructed hole suffix. -/
private def removeTargetLastSavePauseCost
    (pre : Devm) (target lastTarget : B256) : Nat :=
  let M₁ := (pre.memory.read (arrayLengthWord * 32).toNat 32).2
  let afterLength := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := M₁.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  finishLoadWordCost pre arrayLengthWord +
    gVerylow + pushCost (regionWord arrayRegion).toBytes.sig +
    gasColdSload + pushCost ((lastTargetWord * 32).toBytes.sig) +
    gVerylow + afterLength.extCost
      [⟨(lastTargetWord * 32).toNat, 32⟩] +
    removeTargetHolePauseCost loaded target

/- Read the last array entry and save it in `lastTargetWord`, then continue
with the proved hole-overwrite removal suffix. -/
private theorem removeTarget_last_save_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target arrayLength decrementedLength
      removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (harrayLengthRead : Bytes.toB256
      (img.sliceD (arrayLengthWord * 32).toNat 32 0) = arrayLength)
    (hremovedIndexRead : Bytes.toB256
      (img.sliceD (removedIndexWord * 32).toNat 32 0) = removedIndex)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmLength :
      (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmIndex :
      (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hgas : pre.gasLeft =
      G + removeTargetLastSavePauseCost pre target lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (loadWord arrayLengthWord +++ tagTop arrayRegion +++ sload :::
          mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
          loadWord removedIndexWord +++ tagTop arrayRegion +++ sstore :::
          loadWord removedIndexWord +++ lastTargetIndexKey +++ sstore :::
          pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
          sstore ::: loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 :::
          sub ::: pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
          targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M₁ := (pre.memory.read (arrayLengthWord * 32).toNat 32).2
  let afterLength := pre.setMach ⟨[], M₁, 0⟩
  let imgLast := Bytes.writeAt img (lastTargetWord * 32).toNat
    lastTarget.toBytes
  let M₂ := M₁.write (lastTargetWord * 32).toNat lastTarget.toBytes
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  let suffixCost := removeTargetHolePauseCost loaded target
  let tagPushCost := pushCost (regionWord arrayRegion).toBytes.sig
  let offsetPushCost := pushCost ((lastTargetWord * 32).toBytes.sig)
  let mstoreCost := gVerylow + afterLength.extCost
    [⟨(lastTargetWord * 32).toNat, 32⟩]
  let mstoreGas := G + suffixCost + mstoreCost
  let pushGas := mstoreGas + offsetPushCost
  let sloadGas := pushGas + gasColdSload
  let tagGas := sloadGas + gVerylow + tagPushCost
  have hwf₁ : Mem.Wf M₁ := hwf.extend _ _
  have hr₁ : Mem.Reads M₁ img := Mem.Reads.extend hr _ _
  have hwf₂ : Mem.Wf M₂ := Mem.Wf.write hwf₁ _ _
  have hr₂ : Mem.Reads M₂ imgLast := Mem.Reads.write hwf₁ hr₁ _ _
  have harrayLengthValue : Bytes.toB256
      (pre.memory.read (arrayLengthWord * 32).toNat 32).1 = arrayLength := by
    rw [Mem.Reads.read hr]
    exact harrayLengthRead
  have hnewLast : Bytes.toB256
      (imgLast.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnewRead
  have hpreviousLast : Bytes.toB256
      (imgLast.sliceD (previousPauserWord * 32).toNat 32 0) =
        previousPauser := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hpreviousRead
  have htargetLast : Bytes.toB256
      (imgLast.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htargetRead
  have hcontinuationLast : Bytes.toB256
      (imgLast.sliceD (continuationWord * 32).toNat 32 0) = 1 := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hcontinuationRead
  have harrayLengthLast : Bytes.toB256
      (imgLast.sliceD (arrayLengthWord * 32).toNat 32 0) = arrayLength := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact harrayLengthRead
  have hremovedIndexLast : Bytes.toB256
      (imgLast.sliceD (removedIndexWord * 32).toNat 32 0) =
        removedIndex := by
    dsimp only [imgLast]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hremovedIndexRead
  have hlastTargetLast : Bytes.toB256
      (imgLast.sliceD (lastTargetWord * 32).toNat 32 0) = lastTarget := by
    dsimp only [imgLast]
    rw [show 32 = lastTarget.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  let sloadPre := afterLength.setMach
    ⟨arrayEntrySlot arrayLength :: stack, M₁, sloadGas⟩
  have hsloadStack :
      sloadPre.stack = arrayEntrySlot arrayLength :: stack := rfl
  have hsloadValue :
      sloadPre.getStorVal sevm.currentTarget
        (arrayEntrySlot arrayLength) = lastTarget := by
    exact hlastStorage
  have hsloadMemory : sloadPre.memory = M₁ := rfl
  have hsloadGas : gasColdSload ≤ sloadPre.gasLeft := by
    dsimp only [sloadPre, sloadGas, pushGas, mstoreGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sload_revert_step
      (fs := fs) (sevm := sevm)
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (devm := sloadPre)
      (k := arrayEntrySlot arrayLength) (v := lastTarget)
      (s := stack) (M := M₁)
      (rest := mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        sstore ::: loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 :::
        sub ::: pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
        targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
      hsloadStack (by omega) hsloadValue hsloadMemory hsloadGas (by
        intro base c sloadTailGas hkeyAccess haccessSubset hstorage
          hbalances hcode haddresses hrefund hlogs hlower hupper hgasEq
        let spare := gasColdSload - c
        have htailGas : sloadTailGas = pushGas + spare := by
          dsimp only [sloadPre, sloadGas] at hgasEq
          simp only [Devm.gasLeft_setMach] at hgasEq
          dsimp only [spare]
          omega
        let pushPre := base.setMach
          ⟨lastTarget :: stack, M₁, sloadTailGas⟩
        let mstorePre := base.setMach
          ⟨lastTargetWord * 32 :: lastTarget :: stack, M₁,
            G + spare + suffixCost + mstoreCost⟩
        have hmstoreStack : mstorePre.stack =
            lastTargetWord * 32 :: lastTarget :: stack := rfl
        have hmstoreMemory : mstorePre.memory = M₁ := rfl
        have hmstoreCost : gVerylow + mstorePre.extCost
            [⟨(lastTargetWord * 32).toNat, 32⟩] = mstoreCost := by
          dsimp only [mstorePre, mstoreCost, afterLength]
          simp only [Devm.extCost, Devm.memory_setMach]
        have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
          dsimp only [mstorePre]
          simp only [Devm.gasLeft_setMach]
          omega
        rcases directPausePath_mstore_revert_step
            (fs := fs) (sevm := sevm)
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeZeroCode) (devm := mstorePre)
            (i := lastTargetWord * 32) (v := lastTarget)
            (s := stack) (c := mstoreCost) (M := M₁)
            (rest := loadWord lastTargetWord +++
              loadWord removedIndexWord +++ tagTop arrayRegion +++
              sstore ::: loadWord removedIndexWord +++
              lastTargetIndexKey +++ sstore ::: pushB256 0 :::
              loadWord arrayLengthWord +++ tagTop arrayRegion +++ sstore :::
              loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
              pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
              targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
            hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
              intro M' mstoreTailGas hwrite hmstoreGasEq
              have hM' : M' = M₂ := by
                symm
                exact hwrite
              subst M'
              have hmstoreTailGas :
                  mstoreTailGas = G + spare + suffixCost := by
                dsimp only [mstorePre] at hmstoreGasEq
                simp only [Devm.gasLeft_setMach] at hmstoreGasEq
                omega
              let suffixPre := mstorePre.setMach
                ⟨stack, M₂, mstoreTailGas⟩
              have hsuffixStack : suffixPre.stack = stack := rfl
              have hsuffixWf : Mem.Wf suffixPre.memory := hwf₂
              have hsuffixReads : Mem.Reads suffixPre.memory imgLast := hr₂
              have hsuffixCodeSize :
                  (suffixPre.getCode target.toAdr).size = 0 := by
                change (base.getCode target.toAdr).size = 0
                rw [hcode target.toAdr]
                exact hcodeSize
              have hsuffixAccess :
                  target.toAdr ∈ suffixPre.accessedAddresses ∨
                    target.toAdr ∉ suffixPre.accessedAddresses := by
                change target.toAdr ∈ base.accessedAddresses ∨
                  target.toAdr ∉ base.accessedAddresses
                rw [haddresses]
                exact haccess
              have hsuffixWarmHole :
                  (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmHole
              have hsuffixWarmMovedIndex :
                  (⟨sevm.currentTarget, indexSlot lastTarget⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmMovedIndex
              have hsuffixWarmTail :
                  (⟨sevm.currentTarget, arrayEntrySlot arrayLength⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact hkeyAccess
              have hsuffixWarmLength :
                  (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
                    suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmLength
              have hsuffixWarmIndex :
                  (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
                    suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmIndex
              have haccessSetMach (d : Devm) (s' : List B256)
                  (m' : Mem) (g' : Nat) :
                  (d.setMach ⟨s', m', g'⟩).accessedAddresses =
                    d.accessedAddresses := rfl
              have hbaseAddresses :
                  base.accessedAddresses = pre.accessedAddresses := by
                change base.accessedAddresses = pre.accessedAddresses at haddresses
                exact haddresses
              have hmstorePreAddresses :
                  mstorePre.accessedAddresses = pre.accessedAddresses := by
                exact hbaseAddresses
              have hsuffixCostEq :
                  removeTargetHolePauseCost suffixPre target = suffixCost := by
                dsimp only [suffixCost, suffixPre, loaded,
                  removeTargetHolePauseCost,
                  removeTargetMovedIndexPauseCost,
                  removeTargetTailClearPauseCost,
                  removeTargetLengthPauseCost, removeTargetFinalPauseCost,
                  finishSetPauserPauseCost,
                  finishSetPauserPauseSuffixCost,
                  finishSetPauserPauseTerminalCost,
                  finishSetPauserPauseBranchCost,
                  finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
                  finishLoadWordCost]
                simp only [Devm.memory_setMach, Devm.extCost,
                  haccessSetMach]
                rw [hmstorePreAddresses]
              have hsuffixGas : suffixPre.gasLeft =
                  (G + spare) + removeTargetHolePauseCost suffixPre target := by
                simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
                omega
              rcases removeTarget_hole_pause_suffix_runCompiledTo
                  (pre := suffixPre) (G := G + spare) hsuffixStack
                  hsuffixWf hsuffixReads hnewLast hpreviousLast htargetLast
                  hcontinuationLast harrayLengthLast hremovedIndexLast
                  hlastTargetLast hdecrement hlastCanonical hsuffixCodeSize
                  hsuffixAccess hsuffixWarmHole hsuffixWarmMovedIndex
                  hsuffixWarmTail hsuffixWarmLength hsuffixWarmIndex hroom
                  hstatic hemptyLookup hpauseLookup hfinishLookup hsuffixGas
                  with
                ⟨raw, tail, rawOutput, tailPath⟩
              exact ⟨raw, tail, rawOutput, tailPath⟩) with
          ⟨raw, mstoreRun, rawOutput, mstorePath⟩
        have hpushGas : pushPre.gasLeft =
            (G + spare + suffixCost + mstoreCost) + offsetPushCost := by
          simp only [pushPre, Devm.gasLeft_setMach, htailGas]
          dsimp only [pushGas, mstoreGas]
          omega
        rcases directPausePath_prepend_pushB256
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeZeroCode) (pre := pushPre)
            (word := lastTargetWord * 32) (stack := lastTarget :: stack)
            (c := offsetPushCost)
            (G := G + spare + suffixCost + mstoreCost)
            rfl rfl hpushGas (by simp only [List.length_cons]; omega)
            (by simpa only [mstorePre, pushPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
            (by simpa only [mstorePre, pushPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstorePath) with
          ⟨rawRun, rawPath⟩
        exact ⟨raw, by simpa only [mstoreAt, prepend, pushPre] using rawRun,
          rawOutput,
          by simpa only [mstoreAt, prepend, pushPre] using rawPath⟩) with
    ⟨raw, sloadRun, rawOutput, sloadPath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (base := afterLength)
      (region := arrayRegion) (x := arrayLength) (stack := stack)
      (pushGas := tagPushCost) (G := sloadGas) rfl
      (by omega)
      (by simpa only [sloadPre, afterLength, arrayEntrySlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using sloadRun)
      (by simpa only [sloadPre, afterLength, arrayEntrySlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using sloadPath) with
    ⟨tagRun, tagPath⟩
  have hloadGas : pre.gasLeft =
      tagGas + finishLoadWordCost pre arrayLengthWord := by
    rw [hgas]
    dsimp only [removeTargetLastSavePauseCost, M₁, afterLength, M₂,
      loaded, suffixCost, tagPushCost, offsetPushCost, mstoreCost,
      mstoreGas, pushGas, sloadGas, tagGas]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := arrayLengthWord) (value := arrayLength)
      (markedTarget := target) (G := tagGas) hstack harrayLengthValue
      hloadGas (by omega)
      (by simpa only [M₁, afterLength, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [M₁, afterLength, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨run, path⟩
  exact ⟨raw, run, rawOutput, path⟩

/-- Reserved source cost for loading and saving the concrete array length
before the last-target read/save suffix. -/
private def removeTargetLengthSavePauseCost
    (pre : Devm) (target arrayLength lastTarget : B256) : Nat :=
  let M₁ := pre.memory.write (arrayLengthWord * 32).toNat
    arrayLength.toBytes
  let loaded := pre.setMach ⟨[], M₁, 0⟩
  pushCost arrayLengthSlot.toBytes.sig + gasColdSload +
    pushCost ((arrayLengthWord * 32).toBytes.sig) +
    gVerylow + pre.extCost [⟨(arrayLengthWord * 32).toNat, 32⟩] +
    removeTargetLastSavePauseCost loaded target lastTarget

/- Load the concrete array length and save it in `arrayLengthWord`, then
continue with the proved last-target read/save suffix. -/
private theorem removeTarget_length_save_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target arrayLength decrementedLength
      removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hremovedIndexRead : Bytes.toB256
      (img.sliceD (removedIndexWord * 32).toNat 32 0) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmIndex :
      (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hgas : pre.gasLeft = G +
      removeTargetLengthSavePauseCost pre target arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 arrayLengthSlot ::: sload ::: mstoreAt arrayLengthWord +++
          loadWord arrayLengthWord +++ tagTop arrayRegion +++ sload :::
          mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
          loadWord removedIndexWord +++ tagTop arrayRegion +++ sstore :::
          loadWord removedIndexWord +++ lastTargetIndexKey +++ sstore :::
          pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
          sstore ::: loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 :::
          sub ::: pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
          targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let imgLength := Bytes.writeAt img (arrayLengthWord * 32).toNat
    arrayLength.toBytes
  let M₁ := pre.memory.write (arrayLengthWord * 32).toNat
    arrayLength.toBytes
  let loaded := pre.setMach ⟨[], M₁, 0⟩
  let suffixCost := removeTargetLastSavePauseCost loaded target lastTarget
  let slotPushCost := pushCost arrayLengthSlot.toBytes.sig
  let offsetPushCost := pushCost ((arrayLengthWord * 32).toBytes.sig)
  let mstoreCost := gVerylow +
    pre.extCost [⟨(arrayLengthWord * 32).toNat, 32⟩]
  let mstoreGas := G + suffixCost + mstoreCost
  let offsetGas := mstoreGas + offsetPushCost
  let sloadGas := offsetGas + gasColdSload
  have hwf₁ : Mem.Wf M₁ := Mem.Wf.write hwf _ _
  have hr₁ : Mem.Reads M₁ imgLength := Mem.Reads.write hwf hr _ _
  have hnewLength : Bytes.toB256
      (imgLength.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnewRead
  have hpreviousLength : Bytes.toB256
      (imgLength.sliceD (previousPauserWord * 32).toNat 32 0) =
        previousPauser := by
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hpreviousRead
  have htargetLength : Bytes.toB256
      (imgLength.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htargetRead
  have hcontinuationLength : Bytes.toB256
      (imgLength.sliceD (continuationWord * 32).toNat 32 0) = 1 := by
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hcontinuationRead
  have hremovedIndexLength : Bytes.toB256
      (imgLength.sliceD (removedIndexWord * 32).toNat 32 0) =
        removedIndex := by
    dsimp only [imgLength]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hremovedIndexRead
  have harrayLengthLength : Bytes.toB256
      (imgLength.sliceD (arrayLengthWord * 32).toNat 32 0) =
        arrayLength := by
    dsimp only [imgLength]
    rw [show 32 = arrayLength.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  let sloadPre := pre.setMach
    ⟨arrayLengthSlot :: stack, pre.memory, sloadGas⟩
  have hsloadStack : sloadPre.stack = arrayLengthSlot :: stack := rfl
  have hsloadValue :
      sloadPre.getStorVal sevm.currentTarget arrayLengthSlot =
        arrayLength := by
    exact hlengthStorage
  have hsloadMemory : sloadPre.memory = pre.memory := rfl
  have hsloadGas : gasColdSload ≤ sloadPre.gasLeft := by
    dsimp only [sloadPre, sloadGas, offsetGas, mstoreGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sload_revert_step
      (fs := fs) (sevm := sevm)
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (devm := sloadPre)
      (k := arrayLengthSlot) (v := arrayLength)
      (s := stack) (M := pre.memory)
      (rest := mstoreAt arrayLengthWord +++
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ sload :::
        mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        sstore ::: loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 :::
        sub ::: pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
        targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
      hsloadStack (by omega) hsloadValue hsloadMemory hsloadGas (by
        intro base c sloadTailGas hkeyAccess haccessSubset hstorage
          hbalances hcode haddresses hrefund hlogs hlower hupper hgasEq
        let spare := gasColdSload - c
        have htailGas : sloadTailGas = offsetGas + spare := by
          dsimp only [sloadPre, sloadGas] at hgasEq
          simp only [Devm.gasLeft_setMach] at hgasEq
          dsimp only [spare]
          omega
        let offsetPre := base.setMach
          ⟨arrayLength :: stack, pre.memory, sloadTailGas⟩
        let mstorePre := base.setMach
          ⟨arrayLengthWord * 32 :: arrayLength :: stack, pre.memory,
            G + spare + suffixCost + mstoreCost⟩
        have hmstoreStack : mstorePre.stack =
            arrayLengthWord * 32 :: arrayLength :: stack := rfl
        have hmstoreMemory : mstorePre.memory = pre.memory := rfl
        have hmstoreCost : gVerylow + mstorePre.extCost
            [⟨(arrayLengthWord * 32).toNat, 32⟩] = mstoreCost := by
          dsimp only [mstorePre, mstoreCost]
          simp only [Devm.extCost, Devm.memory_setMach]
        have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
          dsimp only [mstorePre]
          simp only [Devm.gasLeft_setMach]
          omega
        rcases directPausePath_mstore_revert_step
            (fs := fs) (sevm := sevm)
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeZeroCode) (devm := mstorePre)
            (i := arrayLengthWord * 32) (v := arrayLength)
            (s := stack) (c := mstoreCost) (M := pre.memory)
            (rest := loadWord arrayLengthWord +++ tagTop arrayRegion +++
              sload ::: mstoreAt lastTargetWord +++
              loadWord lastTargetWord +++ loadWord removedIndexWord +++
              tagTop arrayRegion +++ sstore ::: loadWord removedIndexWord +++
              lastTargetIndexKey +++ sstore ::: pushB256 0 :::
              loadWord arrayLengthWord +++ tagTop arrayRegion +++ sstore :::
              loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
              pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
              targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
            hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
              intro M' mstoreTailGas hwrite hmstoreGasEq
              have hM' : M' = M₁ := by
                symm
                exact hwrite
              subst M'
              have hmstoreTailGas :
                  mstoreTailGas = G + spare + suffixCost := by
                dsimp only [mstorePre] at hmstoreGasEq
                simp only [Devm.gasLeft_setMach] at hmstoreGasEq
                omega
              let suffixPre := mstorePre.setMach
                ⟨stack, M₁, mstoreTailGas⟩
              have hsuffixStack : suffixPre.stack = stack := rfl
              have hsuffixWf : Mem.Wf suffixPre.memory := hwf₁
              have hsuffixReads : Mem.Reads suffixPre.memory imgLength := hr₁
              have hsuffixLastStorage :
                  suffixPre.getStorVal sevm.currentTarget
                    (arrayEntrySlot arrayLength) = lastTarget := by
                change base.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget
                rw [hstorage]
                exact hlastStorage
              have hsuffixCodeSize :
                  (suffixPre.getCode target.toAdr).size = 0 := by
                change (base.getCode target.toAdr).size = 0
                rw [hcode target.toAdr]
                exact hcodeSize
              have hsuffixAccess :
                  target.toAdr ∈ suffixPre.accessedAddresses ∨
                    target.toAdr ∉ suffixPre.accessedAddresses := by
                change target.toAdr ∈ base.accessedAddresses ∨
                  target.toAdr ∉ base.accessedAddresses
                rw [haddresses]
                exact haccess
              have hsuffixWarmHole :
                  (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmHole
              have hsuffixWarmMovedIndex :
                  (⟨sevm.currentTarget, indexSlot lastTarget⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmMovedIndex
              have hsuffixWarmLength :
                  (⟨sevm.currentTarget, arrayLengthSlot⟩ : Adr × B256) ∈
                    suffixPre.accessedStorageKeys := by
                exact hkeyAccess
              have hsuffixWarmIndex :
                  (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
                    suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmIndex
              have haccessSetMach (d : Devm) (s' : List B256)
                  (m' : Mem) (g' : Nat) :
                  (d.setMach ⟨s', m', g'⟩).accessedAddresses =
                    d.accessedAddresses := rfl
              have hbaseAddresses :
                  base.accessedAddresses = pre.accessedAddresses := by
                change base.accessedAddresses = pre.accessedAddresses at haddresses
                exact haddresses
              have hmstorePreAddresses :
                  mstorePre.accessedAddresses = pre.accessedAddresses := by
                exact hbaseAddresses
              have hsuffixCostEq :
                  removeTargetLastSavePauseCost suffixPre target lastTarget =
                    suffixCost := by
                dsimp only [suffixCost, suffixPre, loaded,
                  removeTargetLastSavePauseCost, removeTargetHolePauseCost,
                  removeTargetMovedIndexPauseCost,
                  removeTargetTailClearPauseCost,
                  removeTargetLengthPauseCost, removeTargetFinalPauseCost,
                  finishSetPauserPauseCost,
                  finishSetPauserPauseSuffixCost,
                  finishSetPauserPauseTerminalCost,
                  finishSetPauserPauseBranchCost,
                  finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
                  finishLoadWordCost]
                simp only [Devm.memory_setMach, Devm.extCost,
                  haccessSetMach]
                rw [hmstorePreAddresses]
              have hsuffixGas : suffixPre.gasLeft =
                  (G + spare) +
                    removeTargetLastSavePauseCost suffixPre target
                      lastTarget := by
                simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
                omega
              rcases removeTarget_last_save_pause_suffix_runCompiledTo
                  (pre := suffixPre) (G := G + spare) hsuffixStack
                  hsuffixWf hsuffixReads hnewLength hpreviousLength
                  htargetLength hcontinuationLength harrayLengthLength
                  hremovedIndexLength hdecrement hsuffixLastStorage
                  hlastCanonical hsuffixCodeSize hsuffixAccess
                  hsuffixWarmHole hsuffixWarmMovedIndex hsuffixWarmLength
                  hsuffixWarmIndex hroom hstatic hemptyLookup hpauseLookup
                  hfinishLookup hsuffixGas with
                ⟨raw, tail, rawOutput, tailPath⟩
              exact ⟨raw, tail, rawOutput, tailPath⟩) with
          ⟨raw, mstoreRun, rawOutput, mstorePath⟩
        have hoffsetGas : offsetPre.gasLeft =
            (G + spare + suffixCost + mstoreCost) + offsetPushCost := by
          simp only [offsetPre, Devm.gasLeft_setMach, htailGas]
          dsimp only [offsetGas, mstoreGas]
          omega
        rcases directPausePath_prepend_pushB256
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeZeroCode) (pre := offsetPre)
            (word := arrayLengthWord * 32) (stack := arrayLength :: stack)
            (c := offsetPushCost)
            (G := G + spare + suffixCost + mstoreCost)
            rfl rfl hoffsetGas (by simp only [List.length_cons]; omega)
            (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
            (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstorePath) with
          ⟨rawRun, rawPath⟩
        exact ⟨raw,
          by simpa only [mstoreAt, prepend, offsetPre] using rawRun,
          rawOutput,
          by simpa only [mstoreAt, prepend, offsetPre] using rawPath⟩) with
    ⟨raw, sloadRun, rawOutput, sloadPath⟩
  have hpushGas : pre.gasLeft = sloadGas + slotPushCost := by
    rw [hgas]
    dsimp only [removeTargetLengthSavePauseCost, M₁, loaded,
      suffixCost, slotPushCost, offsetPushCost, mstoreCost, mstoreGas,
      offsetGas, sloadGas]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (pre := pre) (word := arrayLengthSlot)
      (stack := stack) (c := slotPushCost) (G := sloadGas)
      hstack rfl hpushGas (by omega)
      (by simpa only [sloadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using sloadRun)
      (by simpa only [sloadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using sloadPath) with
    ⟨run, path⟩
  exact ⟨raw, run, rawOutput, path⟩

/-- Exact reserved source cost for the complete `removeTarget` body. -/
private def removeTargetPauseCost
    (pre : Devm) (target removedIndex arrayLength lastTarget : B256) : Nat :=
  let M₀ := (pre.memory.read (targetWord * 32).toNat 32).2
  let afterTarget := pre.setMach ⟨[], M₀, 0⟩
  let M₁ := M₀.write (removedIndexWord * 32).toNat removedIndex.toBytes
  let loaded := pre.setMach ⟨[], M₁, 0⟩
  finishLoadWordCost pre targetWord +
    gVerylow + pushCost (regionWord indexRegion).toBytes.sig +
    gasColdSload + pushCost ((removedIndexWord * 32).toBytes.sig) +
    gVerylow + afterTarget.extCost
      [⟨(removedIndexWord * 32).toNat, 32⟩] +
    removeTargetLengthSavePauseCost loaded target arrayLength lastTarget

/- Execute the exact `removeTarget` source body into its proved direct-pause
continuation. -/
private theorem removeTarget_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {newPauser previousPauser target arrayLength decrementedLength
      removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hgas : pre.gasLeft = G + removeTargetPauseCost pre target
      removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre removeTarget
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M₀ := (pre.memory.read (targetWord * 32).toNat 32).2
  let afterTarget := pre.setMach ⟨[], M₀, 0⟩
  let imgIndex := Bytes.writeAt img (removedIndexWord * 32).toNat
    removedIndex.toBytes
  let M₁ := M₀.write (removedIndexWord * 32).toNat removedIndex.toBytes
  let loaded := pre.setMach ⟨[], M₁, 0⟩
  let suffixCost := removeTargetLengthSavePauseCost loaded target
    arrayLength lastTarget
  let tagPushCost := pushCost (regionWord indexRegion).toBytes.sig
  let offsetPushCost := pushCost ((removedIndexWord * 32).toBytes.sig)
  let mstoreCost := gVerylow + afterTarget.extCost
    [⟨(removedIndexWord * 32).toNat, 32⟩]
  let mstoreGas := G + suffixCost + mstoreCost
  let offsetGas := mstoreGas + offsetPushCost
  let sloadGas := offsetGas + gasColdSload
  let tagGas := sloadGas + gVerylow + tagPushCost
  have hwf₀ : Mem.Wf M₀ := hwf.extend _ _
  have hr₀ : Mem.Reads M₀ img := Mem.Reads.extend hr _ _
  have hwf₁ : Mem.Wf M₁ := Mem.Wf.write hwf₀ _ _
  have hr₁ : Mem.Reads M₁ imgIndex := Mem.Reads.write hwf₀ hr₀ _ _
  have htargetValue : Bytes.toB256
      (pre.memory.read (targetWord * 32).toNat 32).1 = target := by
    rw [Mem.Reads.read hr]
    exact htargetRead
  have hnewIndex : Bytes.toB256
      (imgIndex.sliceD (newPauserWord * 32).toNat 32 0) = newPauser := by
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnewRead
  have hpreviousIndex : Bytes.toB256
      (imgIndex.sliceD (previousPauserWord * 32).toNat 32 0) =
        previousPauser := by
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hpreviousRead
  have htargetIndex : Bytes.toB256
      (imgIndex.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htargetRead
  have hcontinuationIndex : Bytes.toB256
      (imgIndex.sliceD (continuationWord * 32).toNat 32 0) = 1 := by
    dsimp only [imgIndex]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hcontinuationRead
  have hremovedIndexIndex : Bytes.toB256
      (imgIndex.sliceD (removedIndexWord * 32).toNat 32 0) =
        removedIndex := by
    dsimp only [imgIndex]
    rw [show 32 = removedIndex.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  let sloadPre := afterTarget.setMach
    ⟨indexSlot target :: stack, M₀, sloadGas⟩
  have hsloadStack : sloadPre.stack = indexSlot target :: stack := rfl
  have hsloadValue :
      sloadPre.getStorVal sevm.currentTarget (indexSlot target) =
        removedIndex := by
    exact hindexStorage
  have hsloadMemory : sloadPre.memory = M₀ := rfl
  have hsloadGas : gasColdSload ≤ sloadPre.gasLeft := by
    dsimp only [sloadPre, sloadGas, offsetGas, mstoreGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sload_revert_step
      (fs := fs) (sevm := sevm)
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (devm := sloadPre)
      (k := indexSlot target) (v := removedIndex)
      (s := stack) (M := M₀)
      (rest := mstoreAt removedIndexWord +++
        pushB256 arrayLengthSlot ::: sload ::: mstoreAt arrayLengthWord +++
        loadWord arrayLengthWord +++ tagTop arrayRegion +++ sload :::
        mstoreAt lastTargetWord +++ loadWord lastTargetWord +++
        loadWord removedIndexWord +++ tagTop arrayRegion +++ sstore :::
        loadWord removedIndexWord +++ lastTargetIndexKey +++ sstore :::
        pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++
        sstore ::: loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 :::
        sub ::: pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
        targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
      hsloadStack (by omega) hsloadValue hsloadMemory hsloadGas (by
        intro base c sloadTailGas hkeyAccess haccessSubset hstorage
          hbalances hcode haddresses hrefund hlogs hlower hupper hgasEq
        let spare := gasColdSload - c
        have htailGas : sloadTailGas = offsetGas + spare := by
          dsimp only [sloadPre, sloadGas] at hgasEq
          simp only [Devm.gasLeft_setMach] at hgasEq
          dsimp only [spare]
          omega
        let offsetPre := base.setMach
          ⟨removedIndex :: stack, M₀, sloadTailGas⟩
        let mstorePre := base.setMach
          ⟨removedIndexWord * 32 :: removedIndex :: stack, M₀,
            G + spare + suffixCost + mstoreCost⟩
        have hmstoreStack : mstorePre.stack =
            removedIndexWord * 32 :: removedIndex :: stack := rfl
        have hmstoreMemory : mstorePre.memory = M₀ := rfl
        have hmstoreCost : gVerylow + mstorePre.extCost
            [⟨(removedIndexWord * 32).toNat, 32⟩] = mstoreCost := by
          dsimp only [mstorePre, mstoreCost, afterTarget]
          simp only [Devm.extCost, Devm.memory_setMach]
        have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
          dsimp only [mstorePre]
          simp only [Devm.gasLeft_setMach]
          omega
        rcases directPausePath_mstore_revert_step
            (fs := fs) (sevm := sevm)
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeZeroCode) (devm := mstorePre)
            (i := removedIndexWord * 32) (v := removedIndex)
            (s := stack) (c := mstoreCost) (M := M₀)
            (rest := pushB256 arrayLengthSlot ::: sload :::
              mstoreAt arrayLengthWord +++ loadWord arrayLengthWord +++
              tagTop arrayRegion +++ sload ::: mstoreAt lastTargetWord +++
              loadWord lastTargetWord +++ loadWord removedIndexWord +++
              tagTop arrayRegion +++ sstore ::: loadWord removedIndexWord +++
              lastTargetIndexKey +++ sstore ::: pushB256 0 :::
              loadWord arrayLengthWord +++ tagTop arrayRegion +++ sstore :::
              loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
              pushB256 arrayLengthSlot ::: sstore ::: pushB256 0 :::
              targetIndexKey +++ sstore ::: .call finishSetPauserSlot)
            hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
              intro M' mstoreTailGas hwrite hmstoreGasEq
              have hM' : M' = M₁ := by
                symm
                exact hwrite
              subst M'
              have hmstoreTailGas :
                  mstoreTailGas = G + spare + suffixCost := by
                dsimp only [mstorePre] at hmstoreGasEq
                simp only [Devm.gasLeft_setMach] at hmstoreGasEq
                omega
              let suffixPre := mstorePre.setMach
                ⟨stack, M₁, mstoreTailGas⟩
              have hsuffixStack : suffixPre.stack = stack := rfl
              have hsuffixWf : Mem.Wf suffixPre.memory := hwf₁
              have hsuffixReads : Mem.Reads suffixPre.memory imgIndex := hr₁
              have hsuffixLengthStorage :
                  suffixPre.getStorVal sevm.currentTarget arrayLengthSlot =
                    arrayLength := by
                change base.getStorVal sevm.currentTarget arrayLengthSlot =
                  arrayLength
                rw [hstorage]
                exact hlengthStorage
              have hsuffixLastStorage :
                  suffixPre.getStorVal sevm.currentTarget
                    (arrayEntrySlot arrayLength) = lastTarget := by
                change base.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget
                rw [hstorage]
                exact hlastStorage
              have hsuffixCodeSize :
                  (suffixPre.getCode target.toAdr).size = 0 := by
                change (base.getCode target.toAdr).size = 0
                rw [hcode target.toAdr]
                exact hcodeSize
              have hsuffixAccess :
                  target.toAdr ∈ suffixPre.accessedAddresses ∨
                    target.toAdr ∉ suffixPre.accessedAddresses := by
                change target.toAdr ∈ base.accessedAddresses ∨
                  target.toAdr ∉ base.accessedAddresses
                rw [haddresses]
                exact haccess
              have hsuffixWarmHole :
                  (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmHole
              have hsuffixWarmMovedIndex :
                  (⟨sevm.currentTarget, indexSlot lastTarget⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmMovedIndex
              have hsuffixWarmIndex :
                  (⟨sevm.currentTarget, indexSlot target⟩ : Adr × B256) ∈
                    suffixPre.accessedStorageKeys := by
                exact hkeyAccess
              have haccessSetMach (d : Devm) (s' : List B256)
                  (m' : Mem) (g' : Nat) :
                  (d.setMach ⟨s', m', g'⟩).accessedAddresses =
                    d.accessedAddresses := rfl
              have hbaseAddresses :
                  base.accessedAddresses = pre.accessedAddresses := by
                change base.accessedAddresses = pre.accessedAddresses at haddresses
                exact haddresses
              have hmstorePreAddresses :
                  mstorePre.accessedAddresses = pre.accessedAddresses := by
                exact hbaseAddresses
              have hsuffixCostEq :
                  removeTargetLengthSavePauseCost suffixPre target
                    arrayLength lastTarget = suffixCost := by
                dsimp only [suffixCost, suffixPre, loaded,
                  removeTargetLengthSavePauseCost,
                  removeTargetLastSavePauseCost, removeTargetHolePauseCost,
                  removeTargetMovedIndexPauseCost,
                  removeTargetTailClearPauseCost,
                  removeTargetLengthPauseCost, removeTargetFinalPauseCost,
                  finishSetPauserPauseCost,
                  finishSetPauserPauseSuffixCost,
                  finishSetPauserPauseTerminalCost,
                  finishSetPauserPauseBranchCost,
                  finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
                  finishLoadWordCost]
                simp only [Devm.memory_setMach, Devm.extCost,
                  haccessSetMach]
                rw [hmstorePreAddresses]
              have hsuffixGas : suffixPre.gasLeft =
                  (G + spare) + removeTargetLengthSavePauseCost suffixPre
                    target arrayLength lastTarget := by
                simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
                omega
              rcases removeTarget_length_save_pause_suffix_runCompiledTo
                  (pre := suffixPre) (G := G + spare) hsuffixStack
                  hsuffixWf hsuffixReads hnewIndex hpreviousIndex
                  htargetIndex hcontinuationIndex hremovedIndexIndex
                  hsuffixLengthStorage hdecrement hsuffixLastStorage
                  hlastCanonical hsuffixCodeSize hsuffixAccess
                  hsuffixWarmHole hsuffixWarmMovedIndex hsuffixWarmIndex
                  hroom hstatic hemptyLookup hpauseLookup hfinishLookup
                  hsuffixGas with
                ⟨raw, tail, rawOutput, tailPath⟩
              exact ⟨raw, tail, rawOutput, tailPath⟩) with
          ⟨raw, mstoreRun, rawOutput, mstorePath⟩
        have hoffsetGas : offsetPre.gasLeft =
            (G + spare + suffixCost + mstoreCost) + offsetPushCost := by
          simp only [offsetPre, Devm.gasLeft_setMach, htailGas]
          dsimp only [offsetGas, mstoreGas]
          omega
        rcases directPausePath_prepend_pushB256
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeZeroCode) (pre := offsetPre)
            (word := removedIndexWord * 32) (stack := removedIndex :: stack)
            (c := offsetPushCost)
            (G := G + spare + suffixCost + mstoreCost)
            rfl rfl hoffsetGas (by simp only [List.length_cons]; omega)
            (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
            (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstorePath) with
          ⟨rawRun, rawPath⟩
        exact ⟨raw,
          by simpa only [mstoreAt, prepend, offsetPre] using rawRun,
          rawOutput,
          by simpa only [mstoreAt, prepend, offsetPre] using rawPath⟩) with
    ⟨raw, sloadRun, rawOutput, sloadPath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (base := afterTarget)
      (region := indexRegion) (x := target) (stack := stack)
      (pushGas := tagPushCost) (G := sloadGas) rfl (by omega)
      (by simpa only [sloadPre, afterTarget, indexSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using sloadRun)
      (by simpa only [sloadPre, afterTarget, indexSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using sloadPath) with
    ⟨tagRun, tagPath⟩
  have hloadGas : pre.gasLeft =
      tagGas + finishLoadWordCost pre targetWord := by
    rw [hgas]
    dsimp only [removeTargetPauseCost, M₀, afterTarget, M₁, loaded,
      suffixCost, tagPushCost, offsetPushCost, mstoreCost, mstoreGas,
      offsetGas, sloadGas, tagGas]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := targetWord) (value := target)
      (markedTarget := target) (G := tagGas) hstack htargetValue
      hloadGas (by omega)
      (by simpa only [M₀, afterTarget, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [M₀, afterTarget, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [removeTarget, targetIndexKey, prepend_append] using run,
    rawOutput,
    by simpa only [removeTarget, targetIndexKey, prepend_append] using path⟩

/-- Exact reserved source cost for the zero-new-pauser branch of
`afterOldPauser`. -/
private def afterOldPauserPauseCost
    (pre : Devm) (target removedIndex arrayLength lastTarget : B256) : Nat :=
  let M := (pre.memory.read (newPauserWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M, 0⟩
  finishLoadWordCost pre newPauserWord + gVerylow +
    (gVerylow + gHigh + gJumpdest) +
    (gVerylow + gMid + gJumpdest) +
    removeTargetPauseCost loaded target removedIndex arrayLength lastTarget

/- The saved zero new-pauser selects the textual removal branch and enters the
exact `removeTarget` body through its internal call. -/
private theorem afterOldPauser_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser target arrayLength decrementedLength removedIndex
      lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hgas : pre.gasLeft = G + afterOldPauserPauseCost pre target
      removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre afterOldPauser
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M := (pre.memory.read (newPauserWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M, 0⟩
  let removeCost := removeTargetPauseCost loaded target removedIndex
    arrayLength lastTarget
  let branchCost := gVerylow + gHigh + gJumpdest
  let callCost := gVerylow + gMid + gJumpdest
  let removePre := pre.setMach ⟨stack, M, G + removeCost⟩
  let callPre := pre.setMach ⟨stack, M, G + removeCost + callCost⟩
  let branchPre := pre.setMach
    ⟨1 :: stack, M, G + removeCost + callCost + branchCost⟩
  let iszeroPre := pre.setMach
    ⟨0 :: stack, M,
      G + removeCost + callCost + branchCost + gVerylow⟩
  have hwfM : Mem.Wf M := hwf.extend _ _
  have hrM : Mem.Reads M img := Mem.Reads.extend hr _ _
  have hnewValue : Bytes.toB256
      (pre.memory.read (newPauserWord * 32).toNat 32).1 = 0 := by
    rw [Mem.Reads.read hr]
    exact hnewRead
  have haccessSetMach (d : Devm) (s' : List B256)
      (m' : Mem) (g' : Nat) :
      (d.setMach ⟨s', m', g'⟩).accessedAddresses =
        d.accessedAddresses := rfl
  have hremoveCostEq :
      removeTargetPauseCost removePre target removedIndex arrayLength
        lastTarget = removeCost := by
    dsimp only [removeCost, removePre, loaded, removeTargetPauseCost,
      removeTargetLengthSavePauseCost, removeTargetLastSavePauseCost,
      removeTargetHolePauseCost, removeTargetMovedIndexPauseCost,
      removeTargetTailClearPauseCost, removeTargetLengthPauseCost,
      removeTargetFinalPauseCost, finishSetPauserPauseCost,
      finishSetPauserPauseSuffixCost, finishSetPauserPauseTerminalCost,
      finishSetPauserPauseBranchCost, finishSetPauserPauseCallCost,
      pauseAfterSetZeroCodeCost, finishLoadWordCost]
    simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
  have hremoveGas : removePre.gasLeft =
      G + removeTargetPauseCost removePre target removedIndex arrayLength
        lastTarget := by
    simp only [removePre, Devm.gasLeft_setMach, hremoveCostEq]
  rcases removeTarget_pause_runCompiledTo
      (pre := removePre) (G := G) (img := img) (stack := stack)
      (previousPauser := previousPauser) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwfM hrM hnewRead hpreviousRead htargetRead hcontinuationRead
      hindexStorage hlengthStorage hdecrement hlastStorage hlastCanonical
      hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic
      hemptyLookup hpauseLookup hfinishLookup hremoveGas with
    ⟨raw, removeRun, rawOutput, removePath⟩
  have hcallRoom : callPre.stack.length < 1024 := by
    simp only [callPre, Devm.stack_setMach]
    omega
  have hcallGas : callPre.gasLeft = removePre.gasLeft + callCost := by
    simp only [callPre, removePre, Devm.gasLeft_setMach]
  have hcallBurn : Devm.BurnBy callCost callPre removePre := by
    convert Devm.burnBy_setMach_gas (devm := callPre)
      (cost := callCost) (G := removePre.gasLeft) hcallGas using 1
    all_goals rfl
  let callRun : Func.RunCompiledTo fs sevm callPre
      (.call removeTargetSlot) (.error (.revert, raw)) :=
    .call hremoveLookup hcallRoom hcallBurn removeRun
  have callPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) callRun :=
    .call (lookup := hremoveLookup) (room := hcallRoom)
      (burn := hcallBurn) (tail := removeRun) removePath
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas : branchPre.gasLeft = callPre.gasLeft + branchCost := by
    simp only [branchPre, callPre, Devm.gasLeft_setMach]
  have hbranchPop : Devm.PopBurnBy [1] branchCost branchPre callPre := by
    convert Devm.popBurnBy_setMach (devm := branchPre) (x := (1 : B256))
      (s := stack) rfl hbranchGas using 1
    all_goals rfl
  let branchRun : Func.RunCompiledTo fs sevm branchPre
      ((.call removeTargetSlot) <?>
        (newCountKey +++ sload ::: pushB256 1 ::: add :::
          newCountKey +++ sstore ::: .call finishSetPauserSlot))
      (.error (.revert, raw)) :=
    .succ (by decide : (1 : B256) ≠ 0) hbranchRoom hbranchPop callRun
  have branchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) branchRun :=
    .succ (nonzero := (by decide : (1 : B256) ≠ 0))
      (room := hbranchRoom) (pop := hbranchPop) (tail := callRun) callPath
  have hiszero : Ninst.RunCompiled sevm iszeroPre iszero branchPre := by
    exact Ninst.runCompiled_unary (by rintro ⟨⟩) rfl rfl rfl (by
      simp only [iszeroPre, Devm.gasLeft_setMach]) (by omega)
  let iszeroRun : Func.RunCompiledTo fs sevm iszeroPre
      (iszero :::
        ((.call removeTargetSlot) <?>
          (newCountKey +++ sload ::: pushB256 1 ::: add :::
            newCountKey +++ sstore ::: .call finishSetPauserSlot)))
      (.error (.revert, raw)) := .next hiszero branchRun
  have iszeroPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) iszeroRun :=
    .next (instructionRun := hiszero) (tail := branchRun) (by simp) branchPath
  have hloadGas : pre.gasLeft =
      (G + removeCost + callCost + branchCost + gVerylow) +
        finishLoadWordCost pre newPauserWord := by
    rw [hgas]
    dsimp only [afterOldPauserPauseCost, M, loaded, removeCost,
      branchCost, callCost]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := newPauserWord) (value := (0 : B256))
      (markedTarget := target)
      (G := G + removeCost + callCost + branchCost + gVerylow)
      hstack hnewValue hloadGas (by omega)
      (by simpa only [M, iszeroPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using iszeroRun)
      (by simpa only [M, iszeroPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using iszeroPath) with
    ⟨run, path⟩
  exact ⟨raw, by simpa only [afterOldPauser] using run, rawOutput,
    by simpa only [afterOldPauser] using path⟩

/-- Worst-case reserved source cost for decrementing the previous pauser count
and entering `afterOldPauser`. -/
private def previousCountDecrementPauseCost
    (pre : Devm) (target removedIndex arrayLength lastTarget : B256) : Nat :=
  let M₁ := (pre.memory.read (previousPauserWord * 32).toNat 32).2
  let afterPrevious := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (previousPauserWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  finishLoadWordCost pre previousPauserWord +
    gVerylow + pushCost (regionWord countRegion).toBytes.sig +
    gasColdSload + pushCost (B256.toBytes 1).sig +
    gVerylow + gVerylow +
    finishLoadWordCost afterPrevious previousPauserWord +
    gVerylow + pushCost (regionWord countRegion).toBytes.sig +
    gasStorageSet + (gVerylow + gMid + gJumpdest) +
    afterOldPauserPauseCost loaded target removedIndex arrayLength lastTarget

/- Decrement the saved previous pauser's count and enter the exact
zero-new-pauser `afterOldPauser` path. -/
private theorem previousCount_decrement_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (htargetCanonical : canonicalAddress target)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hgas : pre.gasLeft = G + previousCountDecrementPauseCost pre target
      removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ sstore ::: .call afterOldPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let M₁ := (pre.memory.read (previousPauserWord * 32).toNat 32).2
  let afterPrevious := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (previousPauserWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  let suffixCost := afterOldPauserPauseCost loaded target removedIndex
    arrayLength lastTarget
  let tagPushCost := pushCost (regionWord countRegion).toBytes.sig
  let onePushCost := pushCost (B256.toBytes 1).sig
  let callCost := gVerylow + gMid + gJumpdest
  let callGas := G + suffixCost + callCost
  let storeGas := callGas + gasStorageSet
  let secondTagGas := storeGas + gVerylow + tagPushCost
  let secondLoadGas := secondTagGas +
    finishLoadWordCost afterPrevious previousPauserWord
  let subGas := secondLoadGas + gVerylow
  let swapGas := subGas + gVerylow
  let onePushGas := swapGas + onePushCost
  let sloadGas := onePushGas + gasColdSload
  let firstTagGas := sloadGas + gVerylow + tagPushCost
  have hwf₁ : Mem.Wf M₁ := hwf.extend _ _
  have hr₁ : Mem.Reads M₁ img := Mem.Reads.extend hr _ _
  have hwf₂ : Mem.Wf M₂ := hwf₁.extend _ _
  have hr₂ : Mem.Reads M₂ img := Mem.Reads.extend hr₁ _ _
  have hpreviousValue : Bytes.toB256
      (pre.memory.read (previousPauserWord * 32).toNat 32).1 =
        previousPauser := by
    rw [Mem.Reads.read hr]
    exact hpreviousRead
  have hpreviousValue₂ : Bytes.toB256
      (M₁.read (previousPauserWord * 32).toNat 32).1 =
        previousPauser := by
    rw [Mem.Reads.read hr₁]
    exact hpreviousRead
  let sloadPre := afterPrevious.setMach
    ⟨countSlot previousPauser :: stack, M₁, sloadGas⟩
  have hsloadStack :
      sloadPre.stack = countSlot previousPauser :: stack := rfl
  have hsloadValue : sloadPre.getStorVal sevm.currentTarget
      (countSlot previousPauser) = countValue := by
    exact hcountStorage
  have hsloadMemory : sloadPre.memory = M₁ := rfl
  have hsloadGas : gasColdSload ≤ sloadPre.gasLeft := by
    dsimp only [sloadPre, sloadGas, onePushGas, swapGas, subGas,
      secondLoadGas, secondTagGas, storeGas, callGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sload_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeZeroCode) (devm := sloadPre)
      (k := countSlot previousPauser) (v := countValue)
      (s := stack) (M := M₁)
      (rest := pushB256 1 ::: swap 0 ::: sub ::: previousCountKey +++
        sstore ::: .call afterOldPauserSlot)
      hsloadStack (by omega) hsloadValue hsloadMemory hsloadGas (by
        intro base c sloadTailGas hkeyAccess haccessSubset hstorage
          hbalances hcode haddresses hrefund hlogs hlower hupper hgasEq
        let sloadSpare := gasColdSload - c
        have hsloadTailGas : sloadTailGas = onePushGas + sloadSpare := by
          dsimp only [sloadPre, sloadGas] at hgasEq
          simp only [Devm.gasLeft_setMach] at hgasEq
          dsimp only [sloadSpare]
          omega
        let storePre := base.setMach
          ⟨countSlot previousPauser :: decrementedCount :: stack, M₂,
            storeGas + sloadSpare⟩
        have hstoreStack : storePre.stack =
            countSlot previousPauser :: decrementedCount :: stack := rfl
        have hstoreWarm :
            (⟨sevm.currentTarget, countSlot previousPauser⟩ : Adr × B256) ∈
              storePre.accessedStorageKeys := hkeyAccess
        have hstoreMemory : storePre.memory = M₂ := rfl
        have hstoreGas : gasStorageSet ≤ storePre.gasLeft := by
          simp only [storePre, Devm.gasLeft_setMach]
          omega
        rcases directPausePath_sstore_warm_revert_step
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeZeroCode) (devm := storePre)
            (k := countSlot previousPauser) (v := decrementedCount)
            (s := stack) (M := M₂) (rest := .call afterOldPauserSlot)
            hstoreStack hstoreWarm hstatic hstoreMemory hstoreGas (by
              intro storeBase storeCost storeTailGas hkey hother hbal hcode₂
                hkeys haddresses₂ hlogs₂ hstoreBound hstoreGasEq
              let storeSpare := gasStorageSet - storeCost
              have hstoreTailGas : storeTailGas =
                  G + sloadSpare + storeSpare + suffixCost + callCost := by
                dsimp only [storePre, storeGas, callGas] at hstoreGasEq
                simp only [Devm.gasLeft_setMach] at hstoreGasEq
                dsimp only [storeSpare]
                omega
              let afterPre := storeBase.setMach
                ⟨stack, M₂, G + sloadSpare + storeSpare + suffixCost⟩
              let afterCallPre := storeBase.setMach
                ⟨stack, M₂, storeTailGas⟩
              have hpair := registryAddressFamilies_pairwise
                htargetCanonical htargetCanonical hpreviousCanonical
              have hlength := registryAddressFamilies_ne_arrayLengthSlot
                htargetCanonical hpreviousCanonical
              have harray := registryAddressFamilies_ne_arrayEntrySlot
                htargetCanonical hpreviousCanonical harrayLengthBound
              have hindexNe :
                  (sevm.currentTarget, indexSlot target) ≠
                    (sevm.currentTarget, countSlot previousPauser) := by
                intro heq
                exact hpair.2.2 (congrArg Prod.snd heq)
              have hlengthNe :
                  (sevm.currentTarget, arrayLengthSlot) ≠
                    (sevm.currentTarget, countSlot previousPauser) := by
                intro heq
                exact hlength.2.2 (congrArg Prod.snd heq).symm
              have harrayNe :
                  (sevm.currentTarget, arrayEntrySlot arrayLength) ≠
                    (sevm.currentTarget, countSlot previousPauser) := by
                intro heq
                exact harray.2.2 (congrArg Prod.snd heq).symm
              have hafterIndex : afterPre.getStorVal sevm.currentTarget
                  (indexSlot target) = removedIndex := by
                change storeBase.getStorVal sevm.currentTarget
                  (indexSlot target) = removedIndex
                rw [hother _ _ hindexNe]
                change base.getStorVal sevm.currentTarget
                  (indexSlot target) = removedIndex
                rw [hstorage]
                exact hindexStorage
              have hafterLength : afterPre.getStorVal sevm.currentTarget
                  arrayLengthSlot = arrayLength := by
                change storeBase.getStorVal sevm.currentTarget
                  arrayLengthSlot = arrayLength
                rw [hother _ _ hlengthNe]
                change base.getStorVal sevm.currentTarget
                  arrayLengthSlot = arrayLength
                rw [hstorage]
                exact hlengthStorage
              have hafterLast : afterPre.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget := by
                change storeBase.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget
                rw [hother _ _ harrayNe]
                change base.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget
                rw [hstorage]
                exact hlastStorage
              have hafterCodeSize :
                  (afterPre.getCode target.toAdr).size = 0 := by
                change (storeBase.getCode target.toAdr).size = 0
                rw [hcode₂ target.toAdr]
                change (base.getCode target.toAdr).size = 0
                rw [hcode target.toAdr]
                exact hcodeSize
              have hafterAccess : target.toAdr ∈ afterPre.accessedAddresses ∨
                  target.toAdr ∉ afterPre.accessedAddresses := by
                change target.toAdr ∈ storeBase.accessedAddresses ∨
                  target.toAdr ∉ storeBase.accessedAddresses
                rw [haddresses₂]
                change target.toAdr ∈ base.accessedAddresses ∨
                  target.toAdr ∉ base.accessedAddresses
                rw [haddresses]
                exact haccess
              have hafterWarmHole :
                  (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
                    Adr × B256) ∈ afterPre.accessedStorageKeys := by
                change (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
                  Adr × B256) ∈ storeBase.accessedStorageKeys
                rw [hkeys]
                change (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
                  Adr × B256) ∈ base.accessedStorageKeys
                exact haccessSubset _ hwarmHole
              have hafterWarmMoved :
                  (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
                    afterPre.accessedStorageKeys := by
                change (⟨sevm.currentTarget, indexSlot lastTarget⟩ :
                  Adr × B256) ∈ storeBase.accessedStorageKeys
                rw [hkeys]
                change (⟨sevm.currentTarget, indexSlot lastTarget⟩ :
                  Adr × B256) ∈ base.accessedStorageKeys
                exact haccessSubset _ hwarmMovedIndex
              have haccessSetMach (d : Devm) (s' : List B256)
                  (m' : Mem) (g' : Nat) :
                  (d.setMach ⟨s', m', g'⟩).accessedAddresses =
                    d.accessedAddresses := rfl
              have hstoreBaseAddresses :
                  storeBase.accessedAddresses = pre.accessedAddresses := by
                rw [haddresses₂]
                change base.accessedAddresses = pre.accessedAddresses
                rw [haddresses]
                rfl
              have hafterCostEq : afterOldPauserPauseCost afterPre target
                  removedIndex arrayLength lastTarget = suffixCost := by
                dsimp only [suffixCost, afterPre, loaded,
                  afterOldPauserPauseCost, removeTargetPauseCost,
                  removeTargetLengthSavePauseCost,
                  removeTargetLastSavePauseCost, removeTargetHolePauseCost,
                  removeTargetMovedIndexPauseCost,
                  removeTargetTailClearPauseCost,
                  removeTargetLengthPauseCost, removeTargetFinalPauseCost,
                  finishSetPauserPauseCost, finishSetPauserPauseSuffixCost,
                  finishSetPauserPauseTerminalCost,
                  finishSetPauserPauseBranchCost,
                  finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
                  finishLoadWordCost]
                simp only [Devm.memory_setMach, Devm.extCost,
                  haccessSetMach]
                rw [hstoreBaseAddresses]
              have hafterGas : afterPre.gasLeft =
                  (G + sloadSpare + storeSpare) +
                    afterOldPauserPauseCost afterPre target removedIndex
                      arrayLength lastTarget := by
                simp only [afterPre, Devm.gasLeft_setMach, hafterCostEq]
              rcases afterOldPauser_pause_runCompiledTo
                  (pre := afterPre) (G := G + sloadSpare + storeSpare)
                  (img := img) (stack := stack) rfl hwf₂ hr₂ hnewRead
                  hpreviousRead htargetRead hcontinuationRead hafterIndex
                  hafterLength hdecrement hafterLast hlastCanonical
                  hafterCodeSize hafterAccess hafterWarmHole hafterWarmMoved
                  hroom hstatic hemptyLookup hpauseLookup hfinishLookup
                  hremoveLookup hafterGas with
                ⟨raw, afterRun, rawOutput, afterPath⟩
              have hcallRoom : afterCallPre.stack.length < 1024 := by
                simp only [afterCallPre, Devm.stack_setMach]
                omega
              have hcallBurn : Devm.BurnBy callCost afterCallPre afterPre := by
                convert Devm.burnBy_setMach_gas (devm := afterCallPre)
                  (cost := callCost) (G := afterPre.gasLeft) (by
                    simp only [afterCallPre, afterPre, Devm.gasLeft_setMach]
                    omega) using 1
                all_goals rfl
              let callRun : Func.RunCompiledTo fs sevm afterCallPre
                  (.call afterOldPauserSlot) (.error (.revert, raw)) :=
                .call hafterLookup hcallRoom hcallBurn afterRun
              have callPath : Func.RunCompiledTo.DirectPausePath
                  sevm.currentTarget target (phase := .beforeZeroCode)
                  callRun :=
                .call (lookup := hafterLookup) (room := hcallRoom)
                  (burn := hcallBurn) (tail := afterRun) afterPath
              exact ⟨raw,
                by simpa only [afterCallPre, Devm.setMach_setMach,
                    Devm.stack_setMach, Devm.memory_setMach,
                    hstoreTailGas] using callRun,
                rawOutput,
                by simpa only [afterCallPre, Devm.setMach_setMach,
                    Devm.stack_setMach, Devm.memory_setMach,
                    hstoreTailGas] using callPath⟩) with
          ⟨raw, storeRun, rawOutput, storePath⟩
        let afterSecond := base.setMach ⟨[], M₂, 0⟩
        rcases directPausePath_prepend_tagTop
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeZeroCode) (base := afterSecond)
            (region := countRegion) (x := previousPauser)
            (stack := decrementedCount :: stack) (pushGas := tagPushCost)
            (G := storeGas + sloadSpare) rfl
            (by simp only [List.length_cons]; omega)
            (by simpa only [storePre, afterSecond, countSlot, secondTagGas,
                Devm.setMach_setMach, Devm.stack_setMach,
                Devm.memory_setMach] using storeRun)
            (by simpa only [storePre, afterSecond, countSlot, secondTagGas,
                Devm.setMach_setMach, Devm.stack_setMach,
                Devm.memory_setMach] using storePath) with
          ⟨tagRun, tagPath⟩
        have hsecondLoadGas :
            (base.setMach ⟨decrementedCount :: stack, M₁,
              secondLoadGas + sloadSpare⟩).gasLeft =
              (storeGas + sloadSpare + gVerylow + tagPushCost) +
                finishLoadWordCost
                (base.setMach ⟨decrementedCount :: stack, M₁,
                  secondLoadGas + sloadSpare⟩) previousPauserWord := by
          simp only [Devm.gasLeft_setMach]
          dsimp only [secondLoadGas, afterPrevious, secondTagGas]
          simp only [finishLoadWordCost, Devm.extCost, Devm.memory_setMach]
          omega
        rcases loadWord_prepend_directPause
            (pre := base.setMach ⟨decrementedCount :: stack, M₁,
              secondLoadGas + sloadSpare⟩)
            (word := previousPauserWord) (value := previousPauser)
            (markedTarget := target)
            (G := storeGas + sloadSpare + gVerylow + tagPushCost)
            rfl hpreviousValue₂ hsecondLoadGas
            (by simp only [Devm.stack_setMach, List.length_cons]; omega)
            (by simpa only [afterSecond, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using tagRun)
            (by simpa only [afterSecond, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
          ⟨secondRun, secondPath⟩
        have hsub : Ninst.RunCompiled sevm
            (base.setMach ⟨countValue :: 1 :: stack, M₁,
              subGas + sloadSpare⟩) sub
            (base.setMach ⟨decrementedCount :: stack, M₁,
              secondLoadGas + sloadSpare⟩) := by
          simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach] using Ninst.runCompiled_binary
              (sevm := sevm) (devm := base.setMach
                ⟨countValue :: 1 :: stack, M₁, subGas + sloadSpare⟩)
              (r := .sub) (f := (· - ·)) (cost := gVerylow)
              (x := countValue) (y := 1) (v := decrementedCount)
              (s := stack) (G := secondLoadGas + sloadSpare)
              (by rintro ⟨⟩) rfl rfl hcountSub (by
                simp only [Devm.gasLeft_setMach]
                dsimp only [subGas]
                omega) (by omega)
        rcases directPausePath_prepend_childless
            (ca := sevm.currentTarget) (target := target) hsub (by simp)
            secondRun secondPath with ⟨subRun, subPath⟩
        have hswap : Ninst.RunCompiled sevm
            (base.setMach ⟨1 :: countValue :: stack, M₁,
              swapGas + sloadSpare⟩) (swap 0)
            (base.setMach ⟨countValue :: 1 :: stack, M₁,
              subGas + sloadSpare⟩) := by
          simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach] using Ninst.runCompiled_swap
              (sevm := sevm) (devm := base.setMach
                ⟨1 :: countValue :: stack, M₁, swapGas + sloadSpare⟩)
              (n := 0) (S := countValue :: 1 :: stack)
              (G := subGas + sloadSpare) rfl (by
                simp only [Devm.gasLeft_setMach]
                dsimp only [swapGas]
                omega)
        rcases directPausePath_prepend_childless
            (ca := sevm.currentTarget) (target := target) hswap (by simp)
            subRun subPath with ⟨swapRun, swapPath⟩
        let pushPre := base.setMach
          ⟨countValue :: stack, M₁, onePushGas + sloadSpare⟩
        have hpushGas : pushPre.gasLeft =
            (swapGas + sloadSpare) + onePushCost := by
          simp only [pushPre, Devm.gasLeft_setMach]
          dsimp only [onePushGas]
          omega
        rcases directPausePath_prepend_pushB256
            (ca := sevm.currentTarget) (target := target) (word := 1)
            (phase := .beforeZeroCode) (pre := pushPre)
            (stack := countValue :: stack) (c := onePushCost)
            (G := swapGas + sloadSpare) rfl rfl hpushGas
            (by simp only [List.length_cons]; omega)
            (by simpa only [pushPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using swapRun)
            (by simpa only [pushPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using swapPath) with
          ⟨pushRun, pushPath⟩
        exact ⟨raw,
          by simpa only [previousCountKey, prepend_append, pushPre,
              hsloadTailGas] using pushRun,
          rawOutput,
          by simpa only [previousCountKey, prepend_append, pushPre,
              hsloadTailGas] using pushPath⟩) with
    ⟨raw, sloadRun, rawOutput, sloadPath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeZeroCode) (base := afterPrevious)
      (region := countRegion) (x := previousPauser) (stack := stack)
      (pushGas := tagPushCost) (G := sloadGas) rfl (by omega)
      (by simpa only [sloadPre, afterPrevious, countSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using sloadRun)
      (by simpa only [sloadPre, afterPrevious, countSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using sloadPath) with
    ⟨tagRun, tagPath⟩
  have hloadGas : pre.gasLeft =
      firstTagGas + finishLoadWordCost pre previousPauserWord := by
    rw [hgas]
    dsimp only [previousCountDecrementPauseCost, M₁, afterPrevious, M₂,
      loaded, suffixCost, tagPushCost, onePushCost, callCost, callGas,
      storeGas, secondTagGas, secondLoadGas, subGas, swapGas, onePushGas,
      sloadGas, firstTagGas]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := previousPauserWord) (value := previousPauser)
      (markedTarget := target) (G := firstTagGas) hstack hpreviousValue
      hloadGas (by omega)
      (by simpa only [M₁, afterPrevious, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [M₁, afterPrevious, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [previousCountKey, prepend_append] using run,
    rawOutput,
    by simpa only [previousCountKey, prepend_append] using path⟩

/-- Exact cost of the nonzero-previous-pauser test and its textual count
decrement branch. -/
private def postAssignmentDecrementPauseCost
    (pre : Devm) (target removedIndex arrayLength lastTarget : B256) : Nat :=
  gVerylow + (gVerylow + gHigh) +
    previousCountDecrementPauseCost pre target removedIndex arrayLength
      lastTarget

/- A nonzero saved previous pauser maps through `iszero` to zero and therefore
takes the textual count-decrement successor of the append branch. -/
private theorem postAssignment_decrement_pause_branch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = previousPauser :: stack)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (htargetCanonical : canonicalAddress target)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hgas : pre.gasLeft = G + postAssignmentDecrementPauseCost pre target
      removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (iszero ::: ((.call appendTargetSlot) <?>
          (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeZeroCode) run := by
  let suffixCost := previousCountDecrementPauseCost pre target removedIndex
    arrayLength lastTarget
  let branchCost := gVerylow + gHigh
  let suffixPre := pre.setMach ⟨stack, pre.memory, G + suffixCost⟩
  let branchPre := pre.setMach
    ⟨0 :: stack, pre.memory, G + suffixCost + branchCost⟩
  have haccessSetMach (d : Devm) (s' : List B256)
      (m' : Mem) (g' : Nat) :
      (d.setMach ⟨s', m', g'⟩).accessedAddresses =
        d.accessedAddresses := rfl
  have hsuffixCostEq : previousCountDecrementPauseCost suffixPre target
      removedIndex arrayLength lastTarget = suffixCost := by
    dsimp only [suffixCost, suffixPre, previousCountDecrementPauseCost,
      afterOldPauserPauseCost, removeTargetPauseCost,
      removeTargetLengthSavePauseCost, removeTargetLastSavePauseCost,
      removeTargetHolePauseCost, removeTargetMovedIndexPauseCost,
      removeTargetTailClearPauseCost, removeTargetLengthPauseCost,
      removeTargetFinalPauseCost, finishSetPauserPauseCost,
      finishSetPauserPauseSuffixCost, finishSetPauserPauseTerminalCost,
      finishSetPauserPauseBranchCost, finishSetPauserPauseCallCost,
      pauseAfterSetZeroCodeCost, finishLoadWordCost]
    simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
  have hsuffixGas : suffixPre.gasLeft =
      G + previousCountDecrementPauseCost suffixPre target removedIndex
        arrayLength lastTarget := by
    simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
  rcases previousCount_decrement_pause_suffix_runCompiledTo
      (pre := suffixPre) (G := G) (img := img) (stack := stack)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwf hr hnewRead hpreviousRead htargetRead hcontinuationRead
      hcountStorage hcountSub hpreviousCanonical htargetCanonical
      harrayLengthBound hindexStorage hlengthStorage hdecrement hlastStorage
      hlastCanonical hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic
      hemptyLookup hpauseLookup hfinishLookup hremoveLookup hafterLookup
      hsuffixGas with
    ⟨raw, suffixRun, rawOutput, suffixPath⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas : branchPre.gasLeft =
      suffixPre.gasLeft + branchCost := by
    simp only [branchPre, suffixPre, Devm.gasLeft_setMach]
  have hbranchPop : Devm.PopBurnBy [0] branchCost branchPre suffixPre := by
    convert Devm.popBurnBy_setMach (devm := branchPre) (x := (0 : B256))
      (s := stack) rfl hbranchGas using 1
    all_goals rfl
  let branchRun : Func.RunCompiledTo fs sevm branchPre
      ((.call appendTargetSlot) <?>
        (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ sstore ::: .call afterOldPauserSlot))
      (.error (.revert, raw)) :=
    .zero hbranchRoom hbranchPop suffixRun
  have branchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) branchRun :=
    .zero (room := hbranchRoom) (pop := hbranchPop)
      (tail := suffixRun) suffixPath
  have hiszero : Ninst.RunCompiled sevm pre iszero branchPre := by
    exact Ninst.runCompiled_unary (by rintro ⟨⟩) rfl hstack (by
      simp [B256.eqCheck, hpreviousNonzero]) (by
      rw [hgas]
      dsimp only [postAssignmentDecrementPauseCost, suffixCost, branchCost]
      omega) (by omega)
  let run : Func.RunCompiledTo fs sevm pre
      (iszero ::: ((.call appendTargetSlot) <?>
        (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
      (.error (.revert, raw)) := .next hiszero branchRun
  have path : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeZeroCode) run :=
    .next (instructionRun := hiszero) (tail := branchRun) (by simp) branchPath
  exact ⟨raw, run, rawOutput, path⟩

/-- Worst-case reserved source cost for the zero assignment write and the
nonzero-previous-pauser branch which follows it. -/
private def assignmentZeroPauseCost
    (pre : Devm) (target removedIndex arrayLength lastTarget : B256) : Nat :=
  let M₁ := (pre.memory.read (newPauserWord * 32).toNat 32).2
  let afterNew := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (targetWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  finishLoadWordCost pre newPauserWord +
    finishLoadWordCost afterNew targetWord +
    gVerylow + pushCost (regionWord assignmentRegion).toBytes.sig +
    gasStorageSet +
    postAssignmentDecrementPauseCost loaded target removedIndex arrayLength
      lastTarget

/- Load the saved zero pauser, derive the target assignment key, perform the
distinguished assignment clear, and enter the exact nonzero-old-pauser branch. -/
private theorem assignment_zero_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = previousPauser :: stack)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) = previousPauser)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (htargetCanonical : canonicalAddress target)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmAssignment :
      (⟨sevm.currentTarget, assignmentSlot target⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hgas : pre.gasLeft = G + assignmentZeroPauseCost pre target
      removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (loadWord newPauserWord +++ targetKey +++ sstore :::
          iszero ::: ((.call appendTargetSlot) <?>
            (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
              previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let M₁ := (pre.memory.read (newPauserWord * 32).toNat 32).2
  let afterNew := pre.setMach ⟨[], M₁, 0⟩
  let M₂ := (M₁.read (targetWord * 32).toNat 32).2
  let loaded := pre.setMach ⟨[], M₂, 0⟩
  let suffixCost := postAssignmentDecrementPauseCost loaded target
    removedIndex arrayLength lastTarget
  let tagPushCost := pushCost (regionWord assignmentRegion).toBytes.sig
  let storeGas := G + suffixCost + gasStorageSet
  let tagGas := storeGas + gVerylow + tagPushCost
  let targetLoadGas := tagGas + finishLoadWordCost afterNew targetWord
  have hwf₁ : Mem.Wf M₁ := hwf.extend _ _
  have hr₁ : Mem.Reads M₁ img := Mem.Reads.extend hr _ _
  have hwf₂ : Mem.Wf M₂ := hwf₁.extend _ _
  have hr₂ : Mem.Reads M₂ img := Mem.Reads.extend hr₁ _ _
  have hnewValue : Bytes.toB256
      (pre.memory.read (newPauserWord * 32).toNat 32).1 = 0 := by
    rw [Mem.Reads.read hr]
    exact hnewRead
  have htargetValue : Bytes.toB256
      (M₁.read (targetWord * 32).toNat 32).1 = target := by
    rw [Mem.Reads.read hr₁]
    exact htargetRead
  let storePre := loaded.setMach
    ⟨assignmentSlot target :: 0 :: previousPauser :: stack, M₂, storeGas⟩
  have hstoreStack : storePre.stack =
      assignmentSlot target :: 0 :: previousPauser :: stack := rfl
  have hstoreWarm :
      (⟨sevm.currentTarget, assignmentSlot target⟩ : Adr × B256) ∈
        storePre.accessedStorageKeys := by
    exact hwarmAssignment
  have hstoreMemory : storePre.memory = M₂ := rfl
  have hstoreGas : gasStorageSet ≤ storePre.gasLeft := by
    simp only [storePre, Devm.gasLeft_setMach]
    omega
  rcases directPausePath_assignment_zero_warm_revert_step
      (ca := sevm.currentTarget) (target := target)
      (fs := fs) (sevm := sevm) (devm := storePre)
      (s := previousPauser :: stack) (M := M₂)
      (rest := iszero ::: ((.call appendTargetSlot) <?>
        (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
      rfl hstoreStack hstoreWarm hstatic hstoreMemory hstoreGas (by
        intro storeBase storeCost storeTailGas hkey hother hbal hcode hkeys
          haddresses hlogs hstoreBound hstoreGasEq
        let storeSpare := gasStorageSet - storeCost
        have hstoreTailGas : storeTailGas = G + storeSpare + suffixCost := by
          dsimp only [storePre, storeGas] at hstoreGasEq
          simp only [Devm.gasLeft_setMach] at hstoreGasEq
          dsimp only [storeSpare]
          omega
        let suffixPre := storeBase.setMach
          ⟨previousPauser :: stack, M₂, storeTailGas⟩
        have hpair := registryAddressFamilies_pairwise
          htargetCanonical htargetCanonical hpreviousCanonical
        have hlength := registryAddressFamilies_ne_arrayLengthSlot
          htargetCanonical hpreviousCanonical
        have harray := registryAddressFamilies_ne_arrayEntrySlot
          htargetCanonical hpreviousCanonical harrayLengthBound
        have hcountNe :
            (sevm.currentTarget, countSlot previousPauser) ≠
              (sevm.currentTarget, assignmentSlot target) := by
          intro heq
          exact hpair.2.1 (congrArg Prod.snd heq).symm
        have hindexNe :
            (sevm.currentTarget, indexSlot target) ≠
              (sevm.currentTarget, assignmentSlot target) := by
          intro heq
          exact hpair.1 (congrArg Prod.snd heq).symm
        have hlengthNe :
            (sevm.currentTarget, arrayLengthSlot) ≠
              (sevm.currentTarget, assignmentSlot target) := by
          intro heq
          exact hlength.1 (congrArg Prod.snd heq).symm
        have harrayNe :
            (sevm.currentTarget, arrayEntrySlot arrayLength) ≠
              (sevm.currentTarget, assignmentSlot target) := by
          intro heq
          exact harray.1 (congrArg Prod.snd heq).symm
        have hsuffixCount : suffixPre.getStorVal sevm.currentTarget
            (countSlot previousPauser) = countValue := by
          change storeBase.getStorVal sevm.currentTarget
            (countSlot previousPauser) = countValue
          rw [hother _ _ hcountNe]
          exact hcountStorage
        have hsuffixIndex : suffixPre.getStorVal sevm.currentTarget
            (indexSlot target) = removedIndex := by
          change storeBase.getStorVal sevm.currentTarget
            (indexSlot target) = removedIndex
          rw [hother _ _ hindexNe]
          exact hindexStorage
        have hsuffixLength : suffixPre.getStorVal sevm.currentTarget
            arrayLengthSlot = arrayLength := by
          change storeBase.getStorVal sevm.currentTarget
            arrayLengthSlot = arrayLength
          rw [hother _ _ hlengthNe]
          exact hlengthStorage
        have hsuffixLast : suffixPre.getStorVal sevm.currentTarget
            (arrayEntrySlot arrayLength) = lastTarget := by
          change storeBase.getStorVal sevm.currentTarget
            (arrayEntrySlot arrayLength) = lastTarget
          rw [hother _ _ harrayNe]
          exact hlastStorage
        have hsuffixCode : (suffixPre.getCode target.toAdr).size = 0 := by
          change (storeBase.getCode target.toAdr).size = 0
          rw [hcode target.toAdr]
          exact hcodeSize
        have hsuffixAccess : target.toAdr ∈ suffixPre.accessedAddresses ∨
            target.toAdr ∉ suffixPre.accessedAddresses := by
          change target.toAdr ∈ storeBase.accessedAddresses ∨
            target.toAdr ∉ storeBase.accessedAddresses
          rw [haddresses]
          exact haccess
        have hsuffixWarmHole :
            (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
              Adr × B256) ∈ suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
            Adr × B256) ∈ storeBase.accessedStorageKeys
          rw [hkeys]
          exact hwarmHole
        have hsuffixWarmMoved :
            (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          change (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
            storeBase.accessedStorageKeys
          rw [hkeys]
          exact hwarmMovedIndex
        have haccessSetMach (d : Devm) (s' : List B256)
            (m' : Mem) (g' : Nat) :
            (d.setMach ⟨s', m', g'⟩).accessedAddresses =
              d.accessedAddresses := rfl
        have hstoreBaseAddresses :
            storeBase.accessedAddresses = pre.accessedAddresses := by
          rw [haddresses]
          rfl
        have hsuffixCostEq : postAssignmentDecrementPauseCost suffixPre target
            removedIndex arrayLength lastTarget = suffixCost := by
          dsimp only [suffixCost, suffixPre, loaded,
            postAssignmentDecrementPauseCost,
            previousCountDecrementPauseCost, afterOldPauserPauseCost,
            removeTargetPauseCost, removeTargetLengthSavePauseCost,
            removeTargetLastSavePauseCost, removeTargetHolePauseCost,
            removeTargetMovedIndexPauseCost, removeTargetTailClearPauseCost,
            removeTargetLengthPauseCost, removeTargetFinalPauseCost,
            finishSetPauserPauseCost, finishSetPauserPauseSuffixCost,
            finishSetPauserPauseTerminalCost, finishSetPauserPauseBranchCost,
            finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
            finishLoadWordCost]
          simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
          rw [hstoreBaseAddresses]
        have hsuffixGas : suffixPre.gasLeft =
            (G + storeSpare) + postAssignmentDecrementPauseCost suffixPre
              target removedIndex arrayLength lastTarget := by
          change storeTailGas =
            (G + storeSpare) + postAssignmentDecrementPauseCost suffixPre
              target removedIndex arrayLength lastTarget
          rw [hsuffixCostEq, hstoreTailGas]
        rcases postAssignment_decrement_pause_branch_runCompiledTo
            (pre := suffixPre) (G := G + storeSpare) (img := img)
            (stack := stack) (previousPauser := previousPauser)
            (countValue := countValue) (decrementedCount := decrementedCount)
            (target := target) (arrayLength := arrayLength)
            (decrementedLength := decrementedLength)
            (removedIndex := removedIndex) (lastTarget := lastTarget)
            rfl hpreviousNonzero hwf₂ hr₂ hnewRead hpreviousRead
            htargetRead hcontinuationRead hsuffixCount hcountSub
            hpreviousCanonical htargetCanonical harrayLengthBound
            hsuffixIndex hsuffixLength hdecrement hsuffixLast hlastCanonical
            hsuffixCode hsuffixAccess hsuffixWarmHole hsuffixWarmMoved hroom
            hstatic hemptyLookup hpauseLookup hfinishLookup hremoveLookup
            hafterLookup hsuffixGas with
          ⟨raw, suffixRun, rawOutput, suffixPath⟩
        exact ⟨raw,
          by simpa only [suffixPre, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using suffixRun,
          rawOutput,
          by simpa only [suffixPre, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using suffixPath⟩) with
    ⟨raw, storeRun, rawOutput, storePath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (base := loaded)
      (region := assignmentRegion) (x := target)
      (stack := 0 :: previousPauser :: stack) (pushGas := tagPushCost)
      (G := storeGas) rfl (by simp only [List.length_cons]; omega)
      (by simpa only [storePre, loaded, assignmentSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using storeRun)
      (by simpa only [storePre, loaded, assignmentSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using storePath) with
    ⟨tagRun, tagPath⟩
  have htargetLoadGas :
      (afterNew.setMach ⟨0 :: previousPauser :: stack, M₁,
        targetLoadGas⟩).gasLeft =
        tagGas + finishLoadWordCost
          (afterNew.setMach ⟨0 :: previousPauser :: stack, M₁,
            targetLoadGas⟩) targetWord := by
    simp only [Devm.gasLeft_setMach]
    dsimp only [targetLoadGas, afterNew, tagGas]
    simp only [finishLoadWordCost, Devm.extCost, Devm.memory_setMach]
  rcases loadWord_prepend_directPause
      (pre := afterNew.setMach
        ⟨0 :: previousPauser :: stack, M₁, targetLoadGas⟩)
      (word := targetWord) (value := target) (markedTarget := target)
      (G := tagGas) rfl htargetValue htargetLoadGas
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
      (by simpa only [loaded, afterNew, tagGas, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [loaded, afterNew, tagGas, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨targetRun, targetPath⟩
  have hnewLoadGas : pre.gasLeft =
      targetLoadGas + finishLoadWordCost pre newPauserWord := by
    rw [hgas]
    dsimp only [assignmentZeroPauseCost, M₁, afterNew, M₂, loaded,
      suffixCost, tagPushCost, storeGas, tagGas, targetLoadGas]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := newPauserWord) (value := 0)
      (markedTarget := target) (G := targetLoadGas) hstack hnewValue
      hnewLoadGas (by simp only [List.length_cons]; omega)
      (by simpa only [M₁, afterNew, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using targetRun)
      (by simpa only [M₁, afterNew, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using targetPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [targetKey, prepend_append] using run,
    rawOutput,
    by simpa only [targetKey, prepend_append] using path⟩

/-- Worst-case reserved source cost for reading and saving the previous
assignment before the distinguished zero assignment write. -/
private def previousAssignmentSavePauseCost
    (pre : Devm) (target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  let M₀ := (pre.memory.read (targetWord * 32).toNat 32).2
  let afterTarget := pre.setMach ⟨[], M₀, 0⟩
  let M₁ := M₀.write (previousPauserWord * 32).toNat
    previousPauser.toBytes
  let loaded := pre.setMach ⟨[], M₁, 0⟩
  finishLoadWordCost pre targetWord +
    gVerylow + pushCost (regionWord assignmentRegion).toBytes.sig +
    gasColdSload + gVerylow +
    pushCost ((previousPauserWord * 32).toBytes.sig) +
    gVerylow + afterTarget.extCost
      [⟨(previousPauserWord * 32).toNat, 32⟩] +
    assignmentZeroPauseCost loaded target removedIndex arrayLength lastTarget

/- Read the target's current assignment, duplicate and save it in scratch
memory, and retain one copy for the exact zero-assignment suffix. -/
private theorem previousAssignment_save_pause_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (htargetCanonical : canonicalAddress target)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hgas : pre.gasLeft = G + previousAssignmentSavePauseCost pre target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
          loadWord newPauserWord +++ targetKey +++ sstore :::
          iszero ::: ((.call appendTargetSlot) <?>
            (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
              previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let M₀ := (pre.memory.read (targetWord * 32).toNat 32).2
  let afterTarget := pre.setMach ⟨[], M₀, 0⟩
  let imgPrev := Bytes.writeAt img (previousPauserWord * 32).toNat
    previousPauser.toBytes
  let M₁ := M₀.write (previousPauserWord * 32).toNat
    previousPauser.toBytes
  let loaded := pre.setMach ⟨[], M₁, 0⟩
  let suffixCost := assignmentZeroPauseCost loaded target removedIndex
    arrayLength lastTarget
  let tagPushCost := pushCost (regionWord assignmentRegion).toBytes.sig
  let offsetPushCost := pushCost ((previousPauserWord * 32).toBytes.sig)
  let mstoreCost := gVerylow + afterTarget.extCost
    [⟨(previousPauserWord * 32).toNat, 32⟩]
  let mstoreGas := G + suffixCost + mstoreCost
  let offsetGas := mstoreGas + offsetPushCost
  let dupGas := offsetGas + gVerylow
  let sloadGas := dupGas + gasColdSload
  let tagGas := sloadGas + gVerylow + tagPushCost
  have hwf₀ : Mem.Wf M₀ := hwf.extend _ _
  have hr₀ : Mem.Reads M₀ img := Mem.Reads.extend hr _ _
  have hwf₁ : Mem.Wf M₁ := Mem.Wf.write hwf₀ _ _
  have hr₁ : Mem.Reads M₁ imgPrev := Mem.Reads.write hwf₀ hr₀ _ _
  have htargetValue : Bytes.toB256
      (pre.memory.read (targetWord * 32).toNat 32).1 = target := by
    rw [Mem.Reads.read hr]
    exact htargetRead
  have hnewPrev : Bytes.toB256
      (imgPrev.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [imgPrev]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnewRead
  have hpreviousPrev : Bytes.toB256
      (imgPrev.sliceD (previousPauserWord * 32).toNat 32 0) =
        previousPauser := by
    dsimp only [imgPrev]
    rw [show 32 = previousPauser.toBytes.length by
      rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have htargetPrev : Bytes.toB256
      (imgPrev.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [imgPrev]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htargetRead
  have hcontinuationPrev : Bytes.toB256
      (imgPrev.sliceD (continuationWord * 32).toNat 32 0) = 1 := by
    dsimp only [imgPrev]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]
      decide)]
    exact hcontinuationRead
  let sloadPre := afterTarget.setMach
    ⟨assignmentSlot target :: stack, M₀, sloadGas⟩
  have hsloadStack : sloadPre.stack = assignmentSlot target :: stack := rfl
  have hsloadValue : sloadPre.getStorVal sevm.currentTarget
      (assignmentSlot target) = previousPauser := by
    exact hassignmentStorage
  have hsloadMemory : sloadPre.memory = M₀ := rfl
  have hsloadGas : gasColdSload ≤ sloadPre.gasLeft := by
    dsimp only [sloadPre, sloadGas, dupGas, offsetGas, mstoreGas]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_sload_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeWrite) (devm := sloadPre)
      (k := assignmentSlot target) (v := previousPauser)
      (s := stack) (M := M₀)
      (rest := dup 0 ::: mstoreAt previousPauserWord +++
        loadWord newPauserWord +++ targetKey +++ sstore :::
        iszero ::: ((.call appendTargetSlot) <?>
          (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
            previousCountKey +++ sstore ::: .call afterOldPauserSlot)))
      hsloadStack (by omega) hsloadValue hsloadMemory hsloadGas (by
        intro base c sloadTailGas hkeyAccess haccessSubset hstorage hbalances
          hcode haddresses hrefund hlogs hlower hupper hgasEq
        let spare := gasColdSload - c
        have htailGas : sloadTailGas = dupGas + spare := by
          dsimp only [sloadPre, sloadGas] at hgasEq
          simp only [Devm.gasLeft_setMach] at hgasEq
          dsimp only [spare]
          omega
        let offsetPre := base.setMach
          ⟨previousPauser :: previousPauser :: stack, M₀,
            offsetGas + spare⟩
        let mstorePre := base.setMach
          ⟨previousPauserWord * 32 :: previousPauser ::
            previousPauser :: stack, M₀,
            G + spare + suffixCost + mstoreCost⟩
        have hmstoreStack : mstorePre.stack = previousPauserWord * 32 ::
            previousPauser :: previousPauser :: stack := rfl
        have hmstoreMemory : mstorePre.memory = M₀ := rfl
        have hmstoreCost : gVerylow + mstorePre.extCost
            [⟨(previousPauserWord * 32).toNat, 32⟩] = mstoreCost := by
          dsimp only [mstorePre, mstoreCost, afterTarget]
          simp only [Devm.extCost, Devm.memory_setMach]
        have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
          dsimp only [mstorePre]
          simp only [Devm.gasLeft_setMach]
          omega
        rcases directPausePath_mstore_revert_step
            (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
            (target := target) (phase := .beforeWrite) (devm := mstorePre)
            (i := previousPauserWord * 32) (v := previousPauser)
            (s := previousPauser :: stack) (c := mstoreCost) (M := M₀)
            (rest := loadWord newPauserWord +++ targetKey +++ sstore :::
              iszero ::: ((.call appendTargetSlot) <?>
                (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 :::
                  sub ::: previousCountKey +++ sstore :::
                  .call afterOldPauserSlot)))
            hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
              intro M' mstoreTailGas hwrite hmstoreGasEq
              have hM' : M' = M₁ := by
                symm
                exact hwrite
              subst M'
              have hmstoreTailGas :
                  mstoreTailGas = G + spare + suffixCost := by
                dsimp only [mstorePre] at hmstoreGasEq
                simp only [Devm.gasLeft_setMach] at hmstoreGasEq
                omega
              let suffixPre := mstorePre.setMach
                ⟨previousPauser :: stack, M₁, mstoreTailGas⟩
              have hsuffixCount : suffixPre.getStorVal sevm.currentTarget
                  (countSlot previousPauser) = countValue := by
                change base.getStorVal sevm.currentTarget
                  (countSlot previousPauser) = countValue
                rw [hstorage]
                exact hcountStorage
              have hsuffixIndex : suffixPre.getStorVal sevm.currentTarget
                  (indexSlot target) = removedIndex := by
                change base.getStorVal sevm.currentTarget
                  (indexSlot target) = removedIndex
                rw [hstorage]
                exact hindexStorage
              have hsuffixLength : suffixPre.getStorVal sevm.currentTarget
                  arrayLengthSlot = arrayLength := by
                change base.getStorVal sevm.currentTarget arrayLengthSlot =
                  arrayLength
                rw [hstorage]
                exact hlengthStorage
              have hsuffixLast : suffixPre.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget := by
                change base.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget
                rw [hstorage]
                exact hlastStorage
              have hsuffixCode :
                  (suffixPre.getCode target.toAdr).size = 0 := by
                change (base.getCode target.toAdr).size = 0
                rw [hcode target.toAdr]
                exact hcodeSize
              have hsuffixAccess :
                  target.toAdr ∈ suffixPre.accessedAddresses ∨
                    target.toAdr ∉ suffixPre.accessedAddresses := by
                change target.toAdr ∈ base.accessedAddresses ∨
                  target.toAdr ∉ base.accessedAddresses
                rw [haddresses]
                exact haccess
              have hsuffixWarmAssignment :
                  (⟨sevm.currentTarget, assignmentSlot target⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact hkeyAccess
              have hsuffixWarmHole :
                  (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmHole
              have hsuffixWarmMoved :
                  (⟨sevm.currentTarget, indexSlot lastTarget⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmMovedIndex
              have haccessSetMach (d : Devm) (s' : List B256)
                  (m' : Mem) (g' : Nat) :
                  (d.setMach ⟨s', m', g'⟩).accessedAddresses =
                    d.accessedAddresses := rfl
              have hbaseAddresses :
                  base.accessedAddresses = pre.accessedAddresses := by
                exact haddresses
              have hmstorePreAddresses :
                  mstorePre.accessedAddresses = pre.accessedAddresses := by
                exact hbaseAddresses
              have hsuffixCostEq : assignmentZeroPauseCost suffixPre target
                  removedIndex arrayLength lastTarget = suffixCost := by
                dsimp only [suffixCost, suffixPre, loaded,
                  assignmentZeroPauseCost, postAssignmentDecrementPauseCost,
                  previousCountDecrementPauseCost, afterOldPauserPauseCost,
                  removeTargetPauseCost, removeTargetLengthSavePauseCost,
                  removeTargetLastSavePauseCost, removeTargetHolePauseCost,
                  removeTargetMovedIndexPauseCost,
                  removeTargetTailClearPauseCost,
                  removeTargetLengthPauseCost, removeTargetFinalPauseCost,
                  finishSetPauserPauseCost, finishSetPauserPauseSuffixCost,
                  finishSetPauserPauseTerminalCost,
                  finishSetPauserPauseBranchCost,
                  finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
                  finishLoadWordCost]
                simp only [Devm.memory_setMach, Devm.extCost,
                  haccessSetMach]
                rw [hmstorePreAddresses]
              have hsuffixGas : suffixPre.gasLeft =
                  (G + spare) + assignmentZeroPauseCost suffixPre target
                    removedIndex arrayLength lastTarget := by
                change mstoreTailGas = (G + spare) +
                  assignmentZeroPauseCost suffixPre target removedIndex
                    arrayLength lastTarget
                rw [hsuffixCostEq, hmstoreTailGas]
              rcases assignment_zero_pause_suffix_runCompiledTo
                  (pre := suffixPre) (G := G + spare) (img := imgPrev)
                  (stack := stack) (previousPauser := previousPauser)
                  (countValue := countValue)
                  (decrementedCount := decrementedCount) (target := target)
                  (arrayLength := arrayLength)
                  (decrementedLength := decrementedLength)
                  (removedIndex := removedIndex) (lastTarget := lastTarget)
                  rfl hpreviousNonzero hwf₁ hr₁ hnewPrev hpreviousPrev
                  htargetPrev hcontinuationPrev hsuffixCount hcountSub
                  hpreviousCanonical htargetCanonical harrayLengthBound
                  hsuffixIndex hsuffixLength hdecrement hsuffixLast
                  hlastCanonical hsuffixCode hsuffixAccess
                  hsuffixWarmAssignment hsuffixWarmHole hsuffixWarmMoved
                  hroom hstatic hemptyLookup hpauseLookup hfinishLookup
                  hremoveLookup hafterLookup hsuffixGas with
                ⟨raw, suffixRun, rawOutput, suffixPath⟩
              exact ⟨raw,
                by simpa only [suffixPre, Devm.setMach_setMach,
                    Devm.stack_setMach, Devm.memory_setMach] using suffixRun,
                rawOutput,
                by simpa only [suffixPre, Devm.setMach_setMach,
                    Devm.stack_setMach,
                    Devm.memory_setMach] using suffixPath⟩) with
          ⟨raw, mstoreRun, rawOutput, mstorePath⟩
        have hoffsetGas : offsetPre.gasLeft =
            (G + spare + suffixCost + mstoreCost) + offsetPushCost := by
          simp only [offsetPre, Devm.gasLeft_setMach]
          dsimp only [offsetGas, mstoreGas]
          omega
        rcases directPausePath_prepend_pushB256
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeWrite) (pre := offsetPre)
            (word := previousPauserWord * 32)
            (stack := previousPauser :: previousPauser :: stack)
            (c := offsetPushCost)
            (G := G + spare + suffixCost + mstoreCost)
            rfl rfl hoffsetGas
            (by simp only [List.length_cons]; omega)
            (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
            (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstorePath) with
          ⟨offsetRun, offsetPath⟩
        have hdup : Ninst.RunCompiled sevm
            (base.setMach
              ⟨previousPauser :: stack, M₀, dupGas + spare⟩)
            (dup 0) offsetPre := by
          simpa only [offsetPre, Devm.setMach_setMach,
            Devm.stack_setMach, Devm.memory_setMach] using
              Ninst.runCompiled_dup
                (sevm := sevm)
                (devm := base.setMach
                  ⟨previousPauser :: stack, M₀, dupGas + spare⟩)
                (n := 0) (w := previousPauser)
                (G := offsetGas + spare) rfl (by
                  simp only [Devm.gasLeft_setMach]
                  dsimp only [dupGas]
                  omega) (by
                  simp only [Devm.stack_setMach, List.length_cons]
                  omega)
        rcases directPausePath_prepend_childless
            (ca := sevm.currentTarget) (target := target) hdup (by simp)
            offsetRun offsetPath with ⟨dupRun, dupPath⟩
        exact ⟨raw,
          by simpa only [mstoreAt, prepend, htailGas] using dupRun,
          rawOutput,
          by simpa only [mstoreAt, prepend, htailGas] using dupPath⟩) with
    ⟨raw, sloadRun, rawOutput, sloadPath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (base := afterTarget)
      (region := assignmentRegion) (x := target) (stack := stack)
      (pushGas := tagPushCost) (G := sloadGas) rfl (by omega)
      (by simpa only [sloadPre, afterTarget, assignmentSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using sloadRun)
      (by simpa only [sloadPre, afterTarget, assignmentSlot,
          Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using sloadPath) with
    ⟨tagRun, tagPath⟩
  have hloadGas : pre.gasLeft =
      tagGas + finishLoadWordCost pre targetWord := by
    rw [hgas]
    dsimp only [previousAssignmentSavePauseCost, M₀, afterTarget, M₁,
      loaded, suffixCost, tagPushCost, offsetPushCost, mstoreCost,
      mstoreGas, offsetGas, dupGas, sloadGas, tagGas]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := targetWord) (value := target)
      (markedTarget := target) (G := tagGas) hstack htargetValue
      hloadGas (by omega)
      (by simpa only [M₀, afterTarget, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [M₀, afterTarget, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [targetKey, prepend_append] using run,
    rawOutput,
    by simpa only [targetKey, prepend_append] using path⟩

/-- Exact reserved cost of the nonzero-target guard followed by the singleton
removal path through the Registry kernel. -/
private def setPauserKernelSingletonRemovalPauseCost
    (pre : Devm) (target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  let M := (pre.memory.read (targetWord * 32).toNat 32).2
  let guarded := pre.setMach ⟨[], M, 0⟩
  finishLoadWordCost pre targetWord + gVerylow + (gVerylow + gHigh) +
    previousAssignmentSavePauseCost guarded target previousPauser
      removedIndex arrayLength lastTarget

/- The nonzero target guard selects the textual Registry body and executes the
complete singleton-removal direct-pause path.  The untaken error call needs no
lookup premise. -/
private theorem setPauserKernel_singletonRemoval_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hgas : pre.gasLeft = G + setPauserKernelSingletonRemovalPauseCost pre
      target previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre setPauserKernel
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let M := (pre.memory.read (targetWord * 32).toNat 32).2
  let guarded := pre.setMach ⟨[], M, 0⟩
  let bodyCost := previousAssignmentSavePauseCost guarded target
    previousPauser removedIndex arrayLength lastTarget
  let branchCost := gVerylow + gHigh
  let bodyPre := pre.setMach ⟨stack, M, G + bodyCost⟩
  let branchPre := pre.setMach
    ⟨0 :: stack, M, G + bodyCost + branchCost⟩
  let iszeroPre := pre.setMach
    ⟨target :: stack, M, G + bodyCost + branchCost + gVerylow⟩
  have hwfM : Mem.Wf M := hwf.extend _ _
  have hrM : Mem.Reads M img := Mem.Reads.extend hr _ _
  have htargetValue : Bytes.toB256
      (pre.memory.read (targetWord * 32).toNat 32).1 = target := by
    rw [Mem.Reads.read hr]
    exact htargetRead
  have hbodyCostEq : previousAssignmentSavePauseCost bodyPre target
      previousPauser removedIndex arrayLength lastTarget = bodyCost := by
    rfl
  have hbodyGas : bodyPre.gasLeft = G +
      previousAssignmentSavePauseCost bodyPre target previousPauser
        removedIndex arrayLength lastTarget := by
    simp only [bodyPre, Devm.gasLeft_setMach, hbodyCostEq]
  rcases previousAssignment_save_pause_suffix_runCompiledTo
      (pre := bodyPre) (G := G) (img := img) (stack := stack)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwfM hrM hnewRead htargetRead hcontinuationRead
      hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage
      hcountSub htargetCanonical harrayLengthBound hindexStorage
      hlengthStorage hdecrement hlastStorage hlastCanonical hcodeSize haccess
      hwarmHole hwarmMovedIndex hroom hstatic hemptyLookup hpauseLookup
      hfinishLookup hremoveLookup hafterLookup hbodyGas with
    ⟨raw, bodyRun, rawOutput, bodyPath⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas : branchPre.gasLeft =
      bodyPre.gasLeft + branchCost := by
    simp only [branchPre, bodyPre, Devm.gasLeft_setMach]
  have hbranchPop : Devm.PopBurnBy [0] branchCost branchPre bodyPre := by
    convert Devm.popBurnBy_setMach (devm := branchPre) (x := (0 : B256))
      (s := stack) rfl hbranchGas using 1
    all_goals rfl
  let branchRun : Func.RunCompiledTo fs sevm branchPre
      ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
          loadWord newPauserWord +++ targetKey +++ sstore :::
          iszero ::: ((.call appendTargetSlot) <?>
            (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
              previousCountKey +++ sstore ::: .call afterOldPauserSlot))))
      (.error (.revert, raw)) :=
    .zero hbranchRoom hbranchPop bodyRun
  have branchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) branchRun :=
    .zero (room := hbranchRoom) (pop := hbranchPop)
      (tail := bodyRun) bodyPath
  have hiszero : Ninst.RunCompiled sevm iszeroPre iszero branchPre := by
    exact Ninst.runCompiled_unary (by rintro ⟨⟩) rfl rfl (by
      simp [B256.eqCheck, htargetNonzero]) (by
      simp only [iszeroPre, Devm.gasLeft_setMach]) (by omega)
  let guardedRun : Func.RunCompiledTo fs sevm iszeroPre
      (iszero ::: ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
          loadWord newPauserWord +++ targetKey +++ sstore :::
          iszero ::: ((.call appendTargetSlot) <?>
            (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
              previousCountKey +++ sstore ::: .call afterOldPauserSlot)))))
      (.error (.revert, raw)) := .next hiszero branchRun
  have guardedPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) guardedRun :=
    .next (instructionRun := hiszero) (tail := branchRun)
      (by simp) branchPath
  have hloadGas : pre.gasLeft =
      (G + bodyCost + branchCost + gVerylow) +
        finishLoadWordCost pre targetWord := by
    rw [hgas]
    dsimp only [setPauserKernelSingletonRemovalPauseCost, M, guarded,
      bodyCost, branchCost]
    omega
  rcases loadWord_prepend_directPause
      (pre := pre) (word := targetWord) (value := target)
      (markedTarget := target)
      (G := G + bodyCost + branchCost + gVerylow)
      hstack htargetValue hloadGas (by omega)
      (by simpa only [M, iszeroPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using guardedRun)
      (by simpa only [M, iszeroPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using guardedPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [setPauserKernel] using run,
    rawOutput,
    by simpa only [setPauserKernel] using path⟩

/- Exact internal call into the singleton-removal Registry kernel, preserving
the marked assignment-write path certificate. -/
private theorem setPauserKernel_call_singletonRemoval_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre kernelPre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : kernelPre.stack = stack)
    (hwf : Mem.Wf kernelPre.memory)
    (hr : Mem.Reads kernelPre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 1)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      kernelPre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      kernelPre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      kernelPre.getStorVal sevm.currentTarget (indexSlot target) =
        removedIndex)
    (hlengthStorage :
      kernelPre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      kernelPre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (kernelPre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ kernelPre.accessedAddresses ∨
      target.toAdr ∉ kernelPre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        kernelPre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        kernelPre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hkernelGas : kernelPre.gasLeft = G +
      setPauserKernelSingletonRemovalPauseCost kernelPre target
        previousPauser removedIndex arrayLength lastTarget)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hcallRoom : pre.stack.length < 1024)
    (hcallBurn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre kernelPre) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (.call setPauserSlot) (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  rcases setPauserKernel_singletonRemoval_pause_runCompiledTo
      (pre := kernelPre) (G := G) (img := img) (stack := stack)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      hstack hwf hr hnewRead htargetRead hcontinuationRead htargetNonzero
      htargetCanonical hassignmentStorage hpreviousNonzero
      hpreviousCanonical hcountStorage hcountSub harrayLengthBound
      hindexStorage hlengthStorage hdecrement hlastStorage hlastCanonical
      hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic hemptyLookup
      hpauseLookup hfinishLookup hremoveLookup hafterLookup hkernelGas with
    ⟨raw, kernelRun, rawOutput, kernelPath⟩
  let run : Func.RunCompiledTo fs sevm pre (.call setPauserSlot)
      (.error (.revert, raw)) :=
    .call hsetPauserLookup hcallRoom hcallBurn kernelRun
  have path : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) run :=
    .call (lookup := hsetPauserLookup) (room := hcallRoom)
      (burn := hcallBurn) (tail := kernelRun) kernelPath
  exact ⟨raw, run, rawOutput, path⟩

/-- Exact reserved cost of saving the continuation selector and calling the
singleton-removal Registry kernel. -/
private def continuationSaveKernelCallPauseCost
    (pre : Devm) (target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  let M := pre.memory.write (continuationWord * 32).toNat (1 : B256).toBytes
  let kernelBase := pre.setMach ⟨[], M, 0⟩
  pushCost (1 : B256).toBytes.sig +
    pushCost ((continuationWord * 32).toBytes.sig) +
    gVerylow + pre.extCost [⟨(continuationWord * 32).toNat, 32⟩] +
    (gVerylow + gMid + gJumpdest) +
    setPauserKernelSingletonRemovalPauseCost kernelBase target
      previousPauser removedIndex arrayLength lastTarget

/- Save continuation selector one, then enter the exact Registry kernel call. -/
private theorem continuation_save_setPauserKernel_call_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + continuationSaveKernelCallPauseCost pre target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 1 ::: mstoreAt continuationWord +++ .call setPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let imgCont := Bytes.writeAt img (continuationWord * 32).toNat
    (1 : B256).toBytes
  let M := pre.memory.write (continuationWord * 32).toNat (1 : B256).toBytes
  let kernelBase := pre.setMach ⟨[], M, 0⟩
  let kernelCost := setPauserKernelSingletonRemovalPauseCost kernelBase target
    previousPauser removedIndex arrayLength lastTarget
  let callCost := gVerylow + gMid + gJumpdest
  let mstoreCost := gVerylow +
    pre.extCost [⟨(continuationWord * 32).toNat, 32⟩]
  let offsetPushCost := pushCost ((continuationWord * 32).toBytes.sig)
  let onePushCost := pushCost (1 : B256).toBytes.sig
  let callPre := pre.setMach
    ⟨stack, M, G + kernelCost + callCost⟩
  let kernelPre := pre.setMach ⟨stack, M, G + kernelCost⟩
  let mstorePre := pre.setMach
    ⟨continuationWord * 32 :: 1 :: stack, pre.memory,
      G + kernelCost + callCost + mstoreCost⟩
  let offsetPre := pre.setMach
    ⟨1 :: stack, pre.memory,
      G + kernelCost + callCost + mstoreCost + offsetPushCost⟩
  have hwfM : Mem.Wf M := Mem.Wf.write hwf _ _
  have hrM : Mem.Reads M imgCont := Mem.Reads.write hwf hr _ _
  have hnewCont : Bytes.toB256
      (imgCont.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [imgCont]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnewRead
  have htargetCont : Bytes.toB256
      (imgCont.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [imgCont]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htargetRead
  have hcontinuationCont : Bytes.toB256
      (imgCont.sliceD (continuationWord * 32).toNat 32 0) = 1 := by
    dsimp only [imgCont]
    rw [show 32 = (1 : B256).toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hkernelCostEq :
      setPauserKernelSingletonRemovalPauseCost kernelPre target
        previousPauser removedIndex arrayLength lastTarget = kernelCost := by
    rfl
  have hkernelGas : kernelPre.gasLeft = G +
      setPauserKernelSingletonRemovalPauseCost kernelPre target
        previousPauser removedIndex arrayLength lastTarget := by
    simp only [kernelPre, Devm.gasLeft_setMach, hkernelCostEq]
  have hcallRoom : callPre.stack.length < 1024 := by
    simp only [callPre, Devm.stack_setMach]
    omega
  have hcallBurn : Devm.BurnBy callCost callPre kernelPre := by
    have hcallGas : callPre.gasLeft = kernelPre.gasLeft + callCost := by
      simp only [callPre, kernelPre, Devm.gasLeft_setMach]
    simpa only [callPre, kernelPre, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach] using
        Devm.burnBy_setMach_gas (devm := callPre) (cost := callCost)
          (G := kernelPre.gasLeft) hcallGas
  rcases setPauserKernel_call_singletonRemoval_pause_runCompiledTo
      (pre := callPre) (kernelPre := kernelPre) (G := G)
      (img := imgCont) (stack := stack)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwfM hrM hnewCont htargetCont hcontinuationCont htargetNonzero
      htargetCanonical hassignmentStorage hpreviousNonzero
      hpreviousCanonical hcountStorage hcountSub harrayLengthBound
      hindexStorage hlengthStorage hdecrement hlastStorage hlastCanonical
      hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic hemptyLookup
      hpauseLookup hfinishLookup hremoveLookup hafterLookup hkernelGas
      hsetPauserLookup hcallRoom hcallBurn with
    ⟨raw, callRun, rawOutput, callPath⟩
  have hmstoreStack : mstorePre.stack =
      continuationWord * 32 :: 1 :: stack := rfl
  have hmstoreMemory : mstorePre.memory = pre.memory := rfl
  have hmstoreCost : gVerylow + mstorePre.extCost
      [⟨(continuationWord * 32).toNat, 32⟩] = mstoreCost := by
    dsimp only [mstorePre, mstoreCost]
    simp only [Devm.extCost, Devm.memory_setMach]
  have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
    simp only [mstorePre, Devm.gasLeft_setMach]
    omega
  rcases directPausePath_mstore_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeWrite) (devm := mstorePre)
      (i := continuationWord * 32) (v := 1) (s := stack)
      (c := mstoreCost) (M := pre.memory) (rest := .call setPauserSlot)
      hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
        intro M' mstoreTailGas hwrite hmstoreGasEq
        have hM' : M' = M := by
          symm
          exact hwrite
        subst M'
        have hmstoreTailGas :
            mstoreTailGas = G + kernelCost + callCost := by
          dsimp only [mstorePre] at hmstoreGasEq
          simp only [Devm.gasLeft_setMach] at hmstoreGasEq
          omega
        exact ⟨raw,
          by simpa only [callPre, mstorePre, M, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach,
              hmstoreTailGas] using callRun,
          rawOutput,
          by simpa only [callPre, mstorePre, M, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach,
              hmstoreTailGas] using callPath⟩) with
    ⟨raw, mstoreRun, rawOutput, mstorePath⟩
  have hoffsetGas : offsetPre.gasLeft =
      (G + kernelCost + callCost + mstoreCost) + offsetPushCost := by
    simp only [offsetPre, Devm.gasLeft_setMach]
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := offsetPre)
      (word := continuationWord * 32) (stack := 1 :: stack)
      (c := offsetPushCost)
      (G := G + kernelCost + callCost + mstoreCost)
      rfl rfl hoffsetGas (by simp only [List.length_cons]; omega)
      (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
      (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using mstorePath) with
    ⟨offsetRun, offsetPath⟩
  have honeGas : pre.gasLeft = offsetPre.gasLeft + onePushCost := by
    rw [hgas]
    dsimp only [continuationSaveKernelCallPauseCost, M, kernelBase,
      kernelCost, callCost, mstoreCost, offsetPushCost, onePushCost,
      offsetPre]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pre) (word := 1) (stack := stack)
      (c := onePushCost) (G := offsetPre.gasLeft)
      hstack rfl honeGas (by omega)
      (by simpa only [offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using offsetRun)
      (by simpa only [offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using offsetPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [mstoreAt, prepend] using run,
    rawOutput,
    by simpa only [mstoreAt, prepend] using path⟩

/-- Exact reserved cost of zeroing the previous-pauser scratch word before
saving the continuation selector and calling the Registry kernel. -/
private def previousZeroContinuationKernelCallPauseCost
    (pre : Devm) (target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  let M := pre.memory.write (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  let saved := pre.setMach ⟨[], M, 0⟩
  pushCost (0 : B256).toBytes.sig +
    pushCost ((previousPauserWord * 32).toBytes.sig) +
    gVerylow + pre.extCost [⟨(previousPauserWord * 32).toNat, 32⟩] +
    continuationSaveKernelCallPauseCost saved target previousPauser
      removedIndex arrayLength lastTarget

/- Zero the previous-pauser scratch word, then execute the exact continuation
save and Registry kernel call. -/
private theorem previous_zero_continuation_kernel_call_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G +
      previousZeroContinuationKernelCallPauseCost pre target previousPauser
        removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 0 ::: mstoreAt previousPauserWord +++
          pushB256 1 ::: mstoreAt continuationWord +++ .call setPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let imgPrev := Bytes.writeAt img (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  let M := pre.memory.write (previousPauserWord * 32).toNat
    (0 : B256).toBytes
  let saved := pre.setMach ⟨[], M, 0⟩
  let suffixCost := continuationSaveKernelCallPauseCost saved target
    previousPauser removedIndex arrayLength lastTarget
  let mstoreCost := gVerylow +
    pre.extCost [⟨(previousPauserWord * 32).toNat, 32⟩]
  let offsetPushCost := pushCost ((previousPauserWord * 32).toBytes.sig)
  let zeroPushCost := pushCost (0 : B256).toBytes.sig
  let suffixPre := pre.setMach ⟨stack, M, G + suffixCost⟩
  let mstorePre := pre.setMach
    ⟨previousPauserWord * 32 :: 0 :: stack, pre.memory,
      G + suffixCost + mstoreCost⟩
  let offsetPre := pre.setMach
    ⟨0 :: stack, pre.memory,
      G + suffixCost + mstoreCost + offsetPushCost⟩
  have hwfM : Mem.Wf M := Mem.Wf.write hwf _ _
  have hrM : Mem.Reads M imgPrev := Mem.Reads.write hwf hr _ _
  have hnewPrev : Bytes.toB256
      (imgPrev.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [imgPrev]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnewRead
  have htargetPrev : Bytes.toB256
      (imgPrev.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [imgPrev]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htargetRead
  have hsuffixCostEq : continuationSaveKernelCallPauseCost suffixPre target
      previousPauser removedIndex arrayLength lastTarget = suffixCost := by
    rfl
  have hsuffixGas : suffixPre.gasLeft = G +
      continuationSaveKernelCallPauseCost suffixPre target previousPauser
        removedIndex arrayLength lastTarget := by
    simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
  rcases continuation_save_setPauserKernel_call_pause_runCompiledTo
      (pre := suffixPre) (G := G) (img := imgPrev) (stack := stack)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwfM hrM hnewPrev htargetPrev htargetNonzero htargetCanonical
      hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage
      hcountSub harrayLengthBound hindexStorage hlengthStorage hdecrement
      hlastStorage hlastCanonical hcodeSize haccess hwarmHole
      hwarmMovedIndex hroom hstatic hemptyLookup hpauseLookup hfinishLookup
      hremoveLookup hafterLookup hsetPauserLookup hsuffixGas with
    ⟨raw, suffixRun, rawOutput, suffixPath⟩
  have hmstoreStack : mstorePre.stack =
      previousPauserWord * 32 :: 0 :: stack := rfl
  have hmstoreMemory : mstorePre.memory = pre.memory := rfl
  have hmstoreCost : gVerylow + mstorePre.extCost
      [⟨(previousPauserWord * 32).toNat, 32⟩] = mstoreCost := by
    dsimp only [mstorePre, mstoreCost]
    simp only [Devm.extCost, Devm.memory_setMach]
  have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
    simp only [mstorePre, Devm.gasLeft_setMach]
    omega
  rcases directPausePath_mstore_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeWrite) (devm := mstorePre)
      (i := previousPauserWord * 32) (v := 0) (s := stack)
      (c := mstoreCost) (M := pre.memory)
      (rest := pushB256 1 ::: mstoreAt continuationWord +++
        .call setPauserSlot)
      hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
        intro M' mstoreTailGas hwrite hmstoreGasEq
        have hM' : M' = M := by
          symm
          exact hwrite
        subst M'
        have hmstoreTailGas : mstoreTailGas = G + suffixCost := by
          dsimp only [mstorePre] at hmstoreGasEq
          simp only [Devm.gasLeft_setMach] at hmstoreGasEq
          omega
        exact ⟨raw,
          by simpa only [suffixPre, mstorePre, M, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach,
              hmstoreTailGas] using suffixRun,
          rawOutput,
          by simpa only [suffixPre, mstorePre, M, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach,
              hmstoreTailGas] using suffixPath⟩) with
    ⟨raw, mstoreRun, rawOutput, mstorePath⟩
  have hoffsetGas : offsetPre.gasLeft =
      (G + suffixCost + mstoreCost) + offsetPushCost := by
    simp only [offsetPre, Devm.gasLeft_setMach]
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := offsetPre)
      (word := previousPauserWord * 32) (stack := 0 :: stack)
      (c := offsetPushCost) (G := G + suffixCost + mstoreCost)
      rfl rfl hoffsetGas (by simp only [List.length_cons]; omega)
      (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
      (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using mstorePath) with
    ⟨offsetRun, offsetPath⟩
  have hzeroGas : pre.gasLeft = offsetPre.gasLeft + zeroPushCost := by
    rw [hgas]
    dsimp only [previousZeroContinuationKernelCallPauseCost, M, saved,
      suffixCost, mstoreCost, offsetPushCost, zeroPushCost, offsetPre]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pre) (word := 0) (stack := stack)
      (c := zeroPushCost) (G := offsetPre.gasLeft)
      hstack rfl hzeroGas (by omega)
      (by simpa only [offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using offsetRun)
      (by simpa only [offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using offsetPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [mstoreAt, prepend] using run,
    rawOutput,
    by simpa only [mstoreAt, prepend] using path⟩

/-- Exact reserved cost of zeroing the new-pauser scratch word before the
previous/continuation saves and Registry kernel call. -/
private def newZeroPreviousContinuationKernelCallPauseCost
    (pre : Devm) (target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  let M := pre.memory.write (newPauserWord * 32).toNat (0 : B256).toBytes
  let saved := pre.setMach ⟨[], M, 0⟩
  pushCost (0 : B256).toBytes.sig +
    pushCost ((newPauserWord * 32).toBytes.sig) +
    gVerylow + pre.extCost [⟨(newPauserWord * 32).toNat, 32⟩] +
    previousZeroContinuationKernelCallPauseCost saved target previousPauser
      removedIndex arrayLength lastTarget

/- Zero the new-pauser scratch word, then execute the exact previous-zero,
continuation-save, and Registry-call suffix. -/
private theorem new_zero_previous_continuation_kernel_call_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G +
      newZeroPreviousContinuationKernelCallPauseCost pre target previousPauser
        removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 0 ::: mstoreAt newPauserWord +++
          pushB256 0 ::: mstoreAt previousPauserWord +++
          pushB256 1 ::: mstoreAt continuationWord +++ .call setPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let imgNew := Bytes.writeAt img (newPauserWord * 32).toNat
    (0 : B256).toBytes
  let M := pre.memory.write (newPauserWord * 32).toNat (0 : B256).toBytes
  let saved := pre.setMach ⟨[], M, 0⟩
  let suffixCost := previousZeroContinuationKernelCallPauseCost saved target
    previousPauser removedIndex arrayLength lastTarget
  let mstoreCost := gVerylow +
    pre.extCost [⟨(newPauserWord * 32).toNat, 32⟩]
  let offsetPushCost := pushCost ((newPauserWord * 32).toBytes.sig)
  let zeroPushCost := pushCost (0 : B256).toBytes.sig
  let suffixPre := pre.setMach ⟨stack, M, G + suffixCost⟩
  let mstorePre := pre.setMach
    ⟨newPauserWord * 32 :: 0 :: stack, pre.memory,
      G + suffixCost + mstoreCost⟩
  let offsetPre := pre.setMach
    ⟨0 :: stack, pre.memory,
      G + suffixCost + mstoreCost + offsetPushCost⟩
  have hwfM : Mem.Wf M := Mem.Wf.write hwf _ _
  have hrM : Mem.Reads M imgNew := Mem.Reads.write hwf hr _ _
  have hnewNew : Bytes.toB256
      (imgNew.sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
    dsimp only [imgNew]
    rw [show 32 = (0 : B256).toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have htargetNew : Bytes.toB256
      (imgNew.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [imgNew]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htargetRead
  have hsuffixCostEq : previousZeroContinuationKernelCallPauseCost suffixPre
      target previousPauser removedIndex arrayLength lastTarget =
        suffixCost := by
    rfl
  have hsuffixGas : suffixPre.gasLeft = G +
      previousZeroContinuationKernelCallPauseCost suffixPre target
        previousPauser removedIndex arrayLength lastTarget := by
    simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
  rcases previous_zero_continuation_kernel_call_pause_runCompiledTo
      (pre := suffixPre) (G := G) (img := imgNew) (stack := stack)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwfM hrM hnewNew htargetNew htargetNonzero htargetCanonical
      hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage
      hcountSub harrayLengthBound hindexStorage hlengthStorage hdecrement
      hlastStorage hlastCanonical hcodeSize haccess hwarmHole
      hwarmMovedIndex hroom hstatic hemptyLookup hpauseLookup hfinishLookup
      hremoveLookup hafterLookup hsetPauserLookup hsuffixGas with
    ⟨raw, suffixRun, rawOutput, suffixPath⟩
  have hmstoreStack : mstorePre.stack =
      newPauserWord * 32 :: 0 :: stack := rfl
  have hmstoreMemory : mstorePre.memory = pre.memory := rfl
  have hmstoreCost : gVerylow + mstorePre.extCost
      [⟨(newPauserWord * 32).toNat, 32⟩] = mstoreCost := by
    dsimp only [mstorePre, mstoreCost]
    simp only [Devm.extCost, Devm.memory_setMach]
  have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
    simp only [mstorePre, Devm.gasLeft_setMach]
    omega
  rcases directPausePath_mstore_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeWrite) (devm := mstorePre)
      (i := newPauserWord * 32) (v := 0) (s := stack)
      (c := mstoreCost) (M := pre.memory)
      (rest := pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 1 ::: mstoreAt continuationWord +++ .call setPauserSlot)
      hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
        intro M' mstoreTailGas hwrite hmstoreGasEq
        have hM' : M' = M := by
          symm
          exact hwrite
        subst M'
        have hmstoreTailGas : mstoreTailGas = G + suffixCost := by
          dsimp only [mstorePre] at hmstoreGasEq
          simp only [Devm.gasLeft_setMach] at hmstoreGasEq
          omega
        exact ⟨raw,
          by simpa only [suffixPre, mstorePre, M, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach,
              hmstoreTailGas] using suffixRun,
          rawOutput,
          by simpa only [suffixPre, mstorePre, M, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach,
              hmstoreTailGas] using suffixPath⟩) with
    ⟨raw, mstoreRun, rawOutput, mstorePath⟩
  have hoffsetGas : offsetPre.gasLeft =
      (G + suffixCost + mstoreCost) + offsetPushCost := by
    simp only [offsetPre, Devm.gasLeft_setMach]
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := offsetPre)
      (word := newPauserWord * 32) (stack := 0 :: stack)
      (c := offsetPushCost) (G := G + suffixCost + mstoreCost)
      rfl rfl hoffsetGas (by simp only [List.length_cons]; omega)
      (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
      (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using mstorePath) with
    ⟨offsetRun, offsetPath⟩
  have hzeroGas : pre.gasLeft = offsetPre.gasLeft + zeroPushCost := by
    rw [hgas]
    dsimp only [newZeroPreviousContinuationKernelCallPauseCost, M, saved,
      suffixCost, mstoreCost, offsetPushCost, zeroPushCost, offsetPre]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pre) (word := 0) (stack := stack)
      (c := zeroPushCost) (G := offsetPre.gasLeft)
      hstack rfl hzeroGas (by omega)
      (by simpa only [offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using offsetRun)
      (by simpa only [offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using offsetPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [mstoreAt, prepend] using run,
    rawOutput,
    by simpa only [mstoreAt, prepend] using path⟩

/-- Exact phase-preserving prepend for ABI argument zero. -/
private theorem directPausePath_prepend_arg_zero
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {value markedTarget : B256} {stack : List B256} {G : Nat}
    {rest : Func} {out : Execution} {phase : DirectPausePhase}
    (hstack : pre.stack = stack)
    (hvalue : Sevm.dataWord sevm 4 = value)
    (hgas : pre.gasLeft =
      G + gVerylow + pushCost (4 : B256).toBytes.sig)
    (hroom : stack.length < 1023)
    (tail : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨value :: stack, pre.memory, G⟩) rest out)
    (tailPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget markedTarget (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (arg 0 +++ rest) out,
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget markedTarget
        (phase := phase) run := by
  have hload : Ninst.RunCompiled sevm
      (pre.setMach ⟨(4 : B256) :: stack, pre.memory, G + gVerylow⟩)
      calldataload
      (pre.setMach ⟨value :: stack, pre.memory, G⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Ninst.runCompiled_calldataload
        (sevm := sevm)
        (devm := pre.setMach
          ⟨(4 : B256) :: stack, pre.memory, G + gVerylow⟩)
        (x := 4) (v := value) (s := stack) (G := G) rfl hvalue
        (by simp only [Devm.gasLeft_setMach])
        (by omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := markedTarget) hload (by simp)
      tail tailPath with ⟨loadRun, loadPath⟩
  have hpushGas : pre.gasLeft =
      (G + gVerylow) + pushCost (4 : B256).toBytes.sig := by
    exact hgas
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := markedTarget)
      (phase := phase) (pre := pre) (word := 4) (stack := stack)
      (c := pushCost (4 : B256).toBytes.sig) (G := G + gVerylow)
      hstack rfl hpushGas (by omega)
      (by simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using loadRun)
      (by simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using loadPath) with
    ⟨run, path⟩
  norm_num [arg, cdl] at *
  exact ⟨run, path⟩

/-- Exact reserved cost of loading ABI argument zero and saving the target
before the three zero/continuation scratch writes and Registry call. -/
private def targetArgSavePauseCost
    (pre : Devm) (target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  let M := pre.memory.write (targetWord * 32).toNat target.toBytes
  let saved := pre.setMach ⟨[], M, 0⟩
  pushCost (4 : B256).toBytes.sig + gVerylow +
    pushCost ((targetWord * 32).toBytes.sig) +
    gVerylow + pre.extCost [⟨(targetWord * 32).toNat, 32⟩] +
    newZeroPreviousContinuationKernelCallPauseCost saved target
      previousPauser removedIndex arrayLength lastTarget

/- Load ABI argument zero, save it as the target scratch word, and execute the
exact zero-new-pauser Registry removal suffix. -/
private theorem target_arg_save_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + targetArgSavePauseCost pre target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (arg 0 +++ mstoreAt targetWord +++
          pushB256 0 ::: mstoreAt newPauserWord +++
          pushB256 0 ::: mstoreAt previousPauserWord +++
          pushB256 1 ::: mstoreAt continuationWord +++ .call setPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let imgTarget := Bytes.writeAt img (targetWord * 32).toNat target.toBytes
  let M := pre.memory.write (targetWord * 32).toNat target.toBytes
  let saved := pre.setMach ⟨[], M, 0⟩
  let suffixCost := newZeroPreviousContinuationKernelCallPauseCost saved
    target previousPauser removedIndex arrayLength lastTarget
  let mstoreCost := gVerylow +
    pre.extCost [⟨(targetWord * 32).toNat, 32⟩]
  let offsetPushCost := pushCost ((targetWord * 32).toBytes.sig)
  let argPushCost := pushCost (4 : B256).toBytes.sig
  let suffixPre := pre.setMach ⟨stack, M, G + suffixCost⟩
  let mstorePre := pre.setMach
    ⟨targetWord * 32 :: target :: stack, pre.memory,
      G + suffixCost + mstoreCost⟩
  let offsetPre := pre.setMach
    ⟨target :: stack, pre.memory,
      G + suffixCost + mstoreCost + offsetPushCost⟩
  have hwfM : Mem.Wf M := Mem.Wf.write hwf _ _
  have hrM : Mem.Reads M imgTarget := Mem.Reads.write hwf hr _ _
  have htargetTarget : Bytes.toB256
      (imgTarget.sliceD (targetWord * 32).toNat 32 0) = target := by
    dsimp only [imgTarget]
    rw [show 32 = target.toBytes.length by rw [B256.length_toBytes]]
    rw [Bytes.sliceD_writeAt, B256.toB256_toBytes]
  have hsuffixCostEq : newZeroPreviousContinuationKernelCallPauseCost
      suffixPre target previousPauser removedIndex arrayLength lastTarget =
        suffixCost := by
    rfl
  have hsuffixGas : suffixPre.gasLeft = G +
      newZeroPreviousContinuationKernelCallPauseCost suffixPre target
        previousPauser removedIndex arrayLength lastTarget := by
    simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
  rcases new_zero_previous_continuation_kernel_call_pause_runCompiledTo
      (pre := suffixPre) (G := G) (img := imgTarget) (stack := stack)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwfM hrM htargetTarget htargetNonzero htargetCanonical
      hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage
      hcountSub harrayLengthBound hindexStorage hlengthStorage hdecrement
      hlastStorage hlastCanonical hcodeSize haccess hwarmHole
      hwarmMovedIndex hroom hstatic hemptyLookup hpauseLookup hfinishLookup
      hremoveLookup hafterLookup hsetPauserLookup hsuffixGas with
    ⟨raw, suffixRun, rawOutput, suffixPath⟩
  have hmstoreStack : mstorePre.stack =
      targetWord * 32 :: target :: stack := rfl
  have hmstoreMemory : mstorePre.memory = pre.memory := rfl
  have hmstoreCost : gVerylow + mstorePre.extCost
      [⟨(targetWord * 32).toNat, 32⟩] = mstoreCost := by
    dsimp only [mstorePre, mstoreCost]
    simp only [Devm.extCost, Devm.memory_setMach]
  have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
    simp only [mstorePre, Devm.gasLeft_setMach]
    omega
  rcases directPausePath_mstore_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeWrite) (devm := mstorePre)
      (i := targetWord * 32) (v := target) (s := stack)
      (c := mstoreCost) (M := pre.memory)
      (rest := pushB256 0 ::: mstoreAt newPauserWord +++
        pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 1 ::: mstoreAt continuationWord +++ .call setPauserSlot)
      hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
        intro M' mstoreTailGas hwrite hmstoreGasEq
        have hM' : M' = M := by
          symm
          exact hwrite
        subst M'
        have hmstoreTailGas : mstoreTailGas = G + suffixCost := by
          dsimp only [mstorePre] at hmstoreGasEq
          simp only [Devm.gasLeft_setMach] at hmstoreGasEq
          omega
        exact ⟨raw,
          by simpa only [suffixPre, mstorePre, M, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach,
              hmstoreTailGas] using suffixRun,
          rawOutput,
          by simpa only [suffixPre, mstorePre, M, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach,
              hmstoreTailGas] using suffixPath⟩) with
    ⟨raw, mstoreRun, rawOutput, mstorePath⟩
  have hoffsetGas : offsetPre.gasLeft =
      (G + suffixCost + mstoreCost) + offsetPushCost := by
    simp only [offsetPre, Devm.gasLeft_setMach]
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := offsetPre)
      (word := targetWord * 32) (stack := target :: stack)
      (c := offsetPushCost) (G := G + suffixCost + mstoreCost)
      rfl rfl hoffsetGas (by simp only [List.length_cons]; omega)
      (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
      (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using mstorePath) with
    ⟨offsetRun, offsetPath⟩
  have hargGas : pre.gasLeft = offsetPre.gasLeft + gVerylow +
      argPushCost := by
    rw [hgas]
    dsimp only [targetArgSavePauseCost, M, saved, suffixCost, mstoreCost,
      offsetPushCost, argPushCost, offsetPre]
    simp only [Devm.gasLeft_setMach]
    omega
  rcases directPausePath_prepend_arg_zero
      (pre := pre) (value := target) (markedTarget := target)
      (stack := stack) (G := offsetPre.gasLeft)
      hstack hdataTarget hargGas (by omega)
      (by simpa only [offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using offsetRun)
      (by simpa only [offsetPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using offsetPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [mstoreAt, prepend] using run,
    rawOutput,
    by simpa only [mstoreAt, prepend] using path⟩

/-- Worst-case reserved cost of reading and saving the pause duration before
the exact target argument and Registry removal suffix. -/
private def pauseDurationSavePauseCost
    (pre : Devm) (duration target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  let M := pre.memory.write (durationWord * 32).toNat duration.toBytes
  let saved := pre.setMach ⟨[], M, 0⟩
  pushCost pauseDurationSlot.toBytes.sig + gasColdSload +
    pushCost ((durationWord * 32).toBytes.sig) +
    gVerylow + pre.extCost [⟨(durationWord * 32).toNat, 32⟩] +
    targetArgSavePauseCost saved target previousPauser removedIndex
      arrayLength lastTarget

/- Read the concrete pause duration, save it in scratch memory, and execute
the complete target-argument singleton-removal suffix. -/
private theorem pauseDuration_save_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {duration previousPauser countValue decrementedCount target arrayLength
      decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + pauseDurationSavePauseCost pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 pauseDurationSlot ::: sload ::: mstoreAt durationWord +++
          arg 0 +++ mstoreAt targetWord +++
          pushB256 0 ::: mstoreAt newPauserWord +++
          pushB256 0 ::: mstoreAt previousPauserWord +++
          pushB256 1 ::: mstoreAt continuationWord +++ .call setPauserSlot)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let imgDuration := Bytes.writeAt img (durationWord * 32).toNat
    duration.toBytes
  let M := pre.memory.write (durationWord * 32).toNat duration.toBytes
  let saved := pre.setMach ⟨[], M, 0⟩
  let suffixCost := targetArgSavePauseCost saved target previousPauser
    removedIndex arrayLength lastTarget
  let mstoreCost := gVerylow +
    pre.extCost [⟨(durationWord * 32).toNat, 32⟩]
  let offsetPushCost := pushCost ((durationWord * 32).toBytes.sig)
  let slotPushCost := pushCost pauseDurationSlot.toBytes.sig
  let mstoreGas := G + suffixCost + mstoreCost
  let offsetGas := mstoreGas + offsetPushCost
  let sloadGas := offsetGas + gasColdSload
  have hwfM : Mem.Wf M := Mem.Wf.write hwf _ _
  have hrM : Mem.Reads M imgDuration := Mem.Reads.write hwf hr _ _
  let sloadPre := pre.setMach
    ⟨pauseDurationSlot :: stack, pre.memory, sloadGas⟩
  have hsloadStack : sloadPre.stack = pauseDurationSlot :: stack := rfl
  have hsloadValue : sloadPre.getStorVal sevm.currentTarget
      pauseDurationSlot = duration := by
    exact hdurationStorage
  have hsloadMemory : sloadPre.memory = pre.memory := rfl
  have hsloadGas : gasColdSload ≤ sloadPre.gasLeft := by
    simp only [sloadPre, Devm.gasLeft_setMach]
    dsimp only [sloadGas, offsetGas, mstoreGas]
    omega
  rcases directPausePath_sload_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeWrite) (devm := sloadPre)
      (k := pauseDurationSlot) (v := duration) (s := stack)
      (M := pre.memory)
      (rest := mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
        pushB256 0 ::: mstoreAt newPauserWord +++
        pushB256 0 ::: mstoreAt previousPauserWord +++
        pushB256 1 ::: mstoreAt continuationWord +++ .call setPauserSlot)
      hsloadStack (by omega) hsloadValue hsloadMemory hsloadGas (by
        intro base c sloadTailGas hkeyAccess haccessSubset hstorage hbalances
          hcode haddresses hrefund hlogs hlower hupper hgasEq
        let spare := gasColdSload - c
        have htailGas : sloadTailGas = offsetGas + spare := by
          dsimp only [sloadPre, sloadGas] at hgasEq
          simp only [Devm.gasLeft_setMach] at hgasEq
          dsimp only [spare]
          omega
        let offsetPre := base.setMach
          ⟨duration :: stack, pre.memory, offsetGas + spare⟩
        let mstorePre := base.setMach
          ⟨durationWord * 32 :: duration :: stack, pre.memory,
            G + spare + suffixCost + mstoreCost⟩
        have hmstoreStack : mstorePre.stack =
            durationWord * 32 :: duration :: stack := rfl
        have hmstoreMemory : mstorePre.memory = pre.memory := rfl
        have hmstoreCost : gVerylow + mstorePre.extCost
            [⟨(durationWord * 32).toNat, 32⟩] = mstoreCost := by
          dsimp only [mstorePre, mstoreCost]
          simp only [Devm.extCost, Devm.memory_setMach]
        have hmstoreGas : mstoreCost ≤ mstorePre.gasLeft := by
          simp only [mstorePre, Devm.gasLeft_setMach]
          omega
        rcases directPausePath_mstore_revert_step
            (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
            (target := target) (phase := .beforeWrite) (devm := mstorePre)
            (i := durationWord * 32) (v := duration) (s := stack)
            (c := mstoreCost) (M := pre.memory)
            (rest := arg 0 +++ mstoreAt targetWord +++
              pushB256 0 ::: mstoreAt newPauserWord +++
              pushB256 0 ::: mstoreAt previousPauserWord +++
              pushB256 1 ::: mstoreAt continuationWord +++
              .call setPauserSlot)
            hmstoreStack hmstoreMemory hmstoreCost hmstoreGas (by
              intro M' mstoreTailGas hwrite hmstoreGasEq
              have hM' : M' = M := by
                symm
                exact hwrite
              subst M'
              have hmstoreTailGas :
                  mstoreTailGas = G + spare + suffixCost := by
                dsimp only [mstorePre] at hmstoreGasEq
                simp only [Devm.gasLeft_setMach] at hmstoreGasEq
                omega
              let suffixPre := mstorePre.setMach
                ⟨stack, M, mstoreTailGas⟩
              have hsuffixAssignment : suffixPre.getStorVal
                  sevm.currentTarget (assignmentSlot target) =
                    previousPauser := by
                change base.getStorVal sevm.currentTarget
                  (assignmentSlot target) = previousPauser
                rw [hstorage]
                exact hassignmentStorage
              have hsuffixCount : suffixPre.getStorVal sevm.currentTarget
                  (countSlot previousPauser) = countValue := by
                change base.getStorVal sevm.currentTarget
                  (countSlot previousPauser) = countValue
                rw [hstorage]
                exact hcountStorage
              have hsuffixIndex : suffixPre.getStorVal sevm.currentTarget
                  (indexSlot target) = removedIndex := by
                change base.getStorVal sevm.currentTarget
                  (indexSlot target) = removedIndex
                rw [hstorage]
                exact hindexStorage
              have hsuffixLength : suffixPre.getStorVal sevm.currentTarget
                  arrayLengthSlot = arrayLength := by
                change base.getStorVal sevm.currentTarget arrayLengthSlot =
                  arrayLength
                rw [hstorage]
                exact hlengthStorage
              have hsuffixLast : suffixPre.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget := by
                change base.getStorVal sevm.currentTarget
                  (arrayEntrySlot arrayLength) = lastTarget
                rw [hstorage]
                exact hlastStorage
              have hsuffixCode :
                  (suffixPre.getCode target.toAdr).size = 0 := by
                change (base.getCode target.toAdr).size = 0
                rw [hcode target.toAdr]
                exact hcodeSize
              have hsuffixAccess :
                  target.toAdr ∈ suffixPre.accessedAddresses ∨
                    target.toAdr ∉ suffixPre.accessedAddresses := by
                change target.toAdr ∈ base.accessedAddresses ∨
                  target.toAdr ∉ base.accessedAddresses
                rw [haddresses]
                exact haccess
              have hsuffixWarmHole :
                  (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmHole
              have hsuffixWarmMoved :
                  (⟨sevm.currentTarget, indexSlot lastTarget⟩ :
                    Adr × B256) ∈ suffixPre.accessedStorageKeys := by
                exact haccessSubset _ hwarmMovedIndex
              have haccessSetMach (d : Devm) (s' : List B256)
                  (m' : Mem) (g' : Nat) :
                  (d.setMach ⟨s', m', g'⟩).accessedAddresses =
                    d.accessedAddresses := rfl
              have hbaseAddresses :
                  base.accessedAddresses = pre.accessedAddresses := by
                exact haddresses
              have hmstorePreAddresses :
                  mstorePre.accessedAddresses = pre.accessedAddresses := by
                exact hbaseAddresses
              have hsuffixCostEq : targetArgSavePauseCost suffixPre target
                  previousPauser removedIndex arrayLength lastTarget =
                    suffixCost := by
                dsimp only [suffixCost, suffixPre, saved,
                  targetArgSavePauseCost,
                  newZeroPreviousContinuationKernelCallPauseCost,
                  previousZeroContinuationKernelCallPauseCost,
                  continuationSaveKernelCallPauseCost,
                  setPauserKernelSingletonRemovalPauseCost,
                  previousAssignmentSavePauseCost, assignmentZeroPauseCost,
                  postAssignmentDecrementPauseCost,
                  previousCountDecrementPauseCost, afterOldPauserPauseCost,
                  removeTargetPauseCost, removeTargetLengthSavePauseCost,
                  removeTargetLastSavePauseCost, removeTargetHolePauseCost,
                  removeTargetMovedIndexPauseCost,
                  removeTargetTailClearPauseCost,
                  removeTargetLengthPauseCost, removeTargetFinalPauseCost,
                  finishSetPauserPauseCost, finishSetPauserPauseSuffixCost,
                  finishSetPauserPauseTerminalCost,
                  finishSetPauserPauseBranchCost,
                  finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
                  finishLoadWordCost]
                simp only [Devm.memory_setMach, Devm.extCost,
                  haccessSetMach]
                rw [hmstorePreAddresses]
              have hsuffixGas : suffixPre.gasLeft =
                  (G + spare) + targetArgSavePauseCost suffixPre target
                    previousPauser removedIndex arrayLength lastTarget := by
                change mstoreTailGas = (G + spare) +
                  targetArgSavePauseCost suffixPre target previousPauser
                    removedIndex arrayLength lastTarget
                rw [hsuffixCostEq, hmstoreTailGas]
              rcases target_arg_save_pause_runCompiledTo
                  (pre := suffixPre) (G := G + spare)
                  (img := imgDuration) (stack := stack)
                  (previousPauser := previousPauser)
                  (countValue := countValue)
                  (decrementedCount := decrementedCount) (target := target)
                  (arrayLength := arrayLength)
                  (decrementedLength := decrementedLength)
                  (removedIndex := removedIndex) (lastTarget := lastTarget)
                  rfl hwfM hrM hdataTarget htargetNonzero htargetCanonical
                  hsuffixAssignment hpreviousNonzero hpreviousCanonical
                  hsuffixCount hcountSub harrayLengthBound hsuffixIndex
                  hsuffixLength hdecrement hsuffixLast hlastCanonical
                  hsuffixCode hsuffixAccess hsuffixWarmHole
                  hsuffixWarmMoved hroom hstatic hemptyLookup hpauseLookup
                  hfinishLookup hremoveLookup hafterLookup hsetPauserLookup
                  hsuffixGas with
                ⟨raw, suffixRun, rawOutput, suffixPath⟩
              exact ⟨raw,
                by simpa only [suffixPre, Devm.setMach_setMach,
                    Devm.stack_setMach, Devm.memory_setMach] using suffixRun,
                rawOutput,
                by simpa only [suffixPre, Devm.setMach_setMach,
                    Devm.stack_setMach,
                    Devm.memory_setMach] using suffixPath⟩) with
          ⟨raw, mstoreRun, rawOutput, mstorePath⟩
        have hoffsetGas : offsetPre.gasLeft =
            (G + spare + suffixCost + mstoreCost) + offsetPushCost := by
          simp only [offsetPre, Devm.gasLeft_setMach]
          dsimp only [offsetGas, mstoreGas]
          omega
        rcases directPausePath_prepend_pushB256
            (ca := sevm.currentTarget) (target := target)
            (phase := .beforeWrite) (pre := offsetPre)
            (word := durationWord * 32) (stack := duration :: stack)
            (c := offsetPushCost)
            (G := G + spare + suffixCost + mstoreCost)
            rfl rfl hoffsetGas
            (by simp only [List.length_cons]; omega)
            (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
                Devm.stack_setMach, Devm.memory_setMach] using mstoreRun)
            (by simpa only [mstorePre, offsetPre, Devm.setMach_setMach,
                Devm.stack_setMach,
                Devm.memory_setMach] using mstorePath) with
          ⟨offsetRun, offsetPath⟩
        exact ⟨raw,
          by simpa only [mstoreAt, prepend, htailGas] using offsetRun,
          rawOutput,
          by simpa only [mstoreAt, prepend, htailGas] using offsetPath⟩) with
    ⟨raw, sloadRun, rawOutput, sloadPath⟩
  have hpushGas : pre.gasLeft = sloadGas + slotPushCost := by
    rw [hgas]
    dsimp only [pauseDurationSavePauseCost, M, saved, suffixCost,
      mstoreCost, offsetPushCost, slotPushCost, mstoreGas, offsetGas,
      sloadGas]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pre) (word := pauseDurationSlot)
      (stack := stack) (c := slotPushCost) (G := sloadGas)
      hstack rfl hpushGas (by omega)
      (by simpa only [sloadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using sloadRun)
      (by simpa only [sloadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using sloadPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [mstoreAt, prepend] using run,
    rawOutput,
    by simpa only [mstoreAt, prepend] using path⟩

/-- Worst-case reserved cost of the live pauser-expiry guard followed by the
complete pause-duration save and singleton-removal suffix. -/
private def liveExpiryPauseCost
    (pre : Devm) (duration target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  gBase + pushCost (regionWord expiryRegion).toBytes.sig + gVerylow +
    gasColdSload + gBase + gVerylow +
    (gVerylow + gHigh + gJumpdest) +
    pauseDurationSavePauseCost pre duration target previousPauser
      removedIndex arrayLength lastTarget

/- The concrete caller's live expiry selects the textual success branch of
the pause guard.  The untaken expired-error call needs no table premise. -/
private theorem liveExpiry_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {pauser expiry duration previousPauser countValue decrementedCount target
      arrayLength decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hcaller : sevm.caller.toB256 = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + liveExpiryPauseCost pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
          ((pushB256 pauseDurationSlot ::: sload :::
            mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
            pushB256 0 ::: mstoreAt newPauserWord +++
            pushB256 0 ::: mstoreAt previousPauserWord +++
            pushB256 1 ::: mstoreAt continuationWord +++
            .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot)))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let suffixCost := pauseDurationSavePauseCost pre duration target
    previousPauser removedIndex arrayLength lastTarget
  let branchCost := gVerylow + gHigh + gJumpdest
  let tagPushCost := pushCost (regionWord expiryRegion).toBytes.sig
  let branchGas := G + suffixCost + branchCost
  let ltGas := branchGas + gVerylow
  let timestampGas := ltGas + gBase
  let sloadGas := timestampGas + gasColdSload
  let tagGas := sloadGas + gVerylow + tagPushCost
  let sloadPre := pre.setMach
    ⟨expirySlot pauser :: stack, pre.memory, sloadGas⟩
  have hsloadStack : sloadPre.stack = expirySlot pauser :: stack := rfl
  have hsloadValue : sloadPre.getStorVal sevm.currentTarget
      (expirySlot pauser) = expiry := by
    exact hexpiryStorage
  have hsloadMemory : sloadPre.memory = pre.memory := rfl
  have hsloadGas : gasColdSload ≤ sloadPre.gasLeft := by
    simp only [sloadPre, Devm.gasLeft_setMach]
    dsimp only [sloadGas, timestampGas, ltGas, branchGas]
    omega
  rcases directPausePath_sload_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeWrite) (devm := sloadPre)
      (k := expirySlot pauser) (v := expiry) (s := stack)
      (M := pre.memory)
      (rest := timestamp ::: lt :::
        ((pushB256 pauseDurationSlot ::: sload :::
          mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
          pushB256 0 ::: mstoreAt newPauserWord +++
          pushB256 0 ::: mstoreAt previousPauserWord +++
          pushB256 1 ::: mstoreAt continuationWord +++
          .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot)))
      hsloadStack (by omega) hsloadValue hsloadMemory hsloadGas (by
        intro base c sloadTailGas hkeyAccess haccessSubset hstorage hbalances
          hcode haddresses hrefund hlogs hlower hupper hgasEq
        let spare := gasColdSload - c
        have htailGas : sloadTailGas = timestampGas + spare := by
          dsimp only [sloadPre, sloadGas] at hgasEq
          simp only [Devm.gasLeft_setMach] at hgasEq
          dsimp only [spare]
          omega
        let suffixPre := base.setMach
          ⟨stack, pre.memory, G + spare + suffixCost⟩
        let branchPre := base.setMach
          ⟨1 :: stack, pre.memory, spare + branchGas⟩
        let ltPre := base.setMach
          ⟨sevm.benvStat.time :: expiry :: stack, pre.memory,
            spare + ltGas⟩
        let timestampPre := base.setMach
          ⟨expiry :: stack, pre.memory, sloadTailGas⟩
        have hsuffixDuration : suffixPre.getStorVal sevm.currentTarget
            pauseDurationSlot = duration := by
          change base.getStorVal sevm.currentTarget pauseDurationSlot =
            duration
          rw [hstorage]
          exact hdurationStorage
        have hsuffixAssignment : suffixPre.getStorVal sevm.currentTarget
            (assignmentSlot target) = previousPauser := by
          change base.getStorVal sevm.currentTarget
            (assignmentSlot target) = previousPauser
          rw [hstorage]
          exact hassignmentStorage
        have hsuffixCount : suffixPre.getStorVal sevm.currentTarget
            (countSlot previousPauser) = countValue := by
          change base.getStorVal sevm.currentTarget
            (countSlot previousPauser) = countValue
          rw [hstorage]
          exact hcountStorage
        have hsuffixIndex : suffixPre.getStorVal sevm.currentTarget
            (indexSlot target) = removedIndex := by
          change base.getStorVal sevm.currentTarget (indexSlot target) =
            removedIndex
          rw [hstorage]
          exact hindexStorage
        have hsuffixLength : suffixPre.getStorVal sevm.currentTarget
            arrayLengthSlot = arrayLength := by
          change base.getStorVal sevm.currentTarget arrayLengthSlot =
            arrayLength
          rw [hstorage]
          exact hlengthStorage
        have hsuffixLast : suffixPre.getStorVal sevm.currentTarget
            (arrayEntrySlot arrayLength) = lastTarget := by
          change base.getStorVal sevm.currentTarget
            (arrayEntrySlot arrayLength) = lastTarget
          rw [hstorage]
          exact hlastStorage
        have hsuffixCode : (suffixPre.getCode target.toAdr).size = 0 := by
          change (base.getCode target.toAdr).size = 0
          rw [hcode target.toAdr]
          exact hcodeSize
        have hsuffixAccess : target.toAdr ∈ suffixPre.accessedAddresses ∨
            target.toAdr ∉ suffixPre.accessedAddresses := by
          change target.toAdr ∈ base.accessedAddresses ∨
            target.toAdr ∉ base.accessedAddresses
          rw [haddresses]
          exact haccess
        have hsuffixWarmHole :
            (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
              Adr × B256) ∈ suffixPre.accessedStorageKeys := by
          exact haccessSubset _ hwarmHole
        have hsuffixWarmMoved :
            (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          exact haccessSubset _ hwarmMovedIndex
        have haccessSetMach (d : Devm) (s' : List B256)
            (m' : Mem) (g' : Nat) :
            (d.setMach ⟨s', m', g'⟩).accessedAddresses =
              d.accessedAddresses := rfl
        have hbaseAddresses :
            base.accessedAddresses = pre.accessedAddresses := by
          exact haddresses
        have hsuffixCostEq : pauseDurationSavePauseCost suffixPre duration
            target previousPauser removedIndex arrayLength lastTarget =
              suffixCost := by
          dsimp only [suffixCost, suffixPre, pauseDurationSavePauseCost,
            targetArgSavePauseCost,
            newZeroPreviousContinuationKernelCallPauseCost,
            previousZeroContinuationKernelCallPauseCost,
            continuationSaveKernelCallPauseCost,
            setPauserKernelSingletonRemovalPauseCost,
            previousAssignmentSavePauseCost, assignmentZeroPauseCost,
            postAssignmentDecrementPauseCost,
            previousCountDecrementPauseCost, afterOldPauserPauseCost,
            removeTargetPauseCost, removeTargetLengthSavePauseCost,
            removeTargetLastSavePauseCost, removeTargetHolePauseCost,
            removeTargetMovedIndexPauseCost,
            removeTargetTailClearPauseCost, removeTargetLengthPauseCost,
            removeTargetFinalPauseCost, finishSetPauserPauseCost,
            finishSetPauserPauseSuffixCost,
            finishSetPauserPauseTerminalCost,
            finishSetPauserPauseBranchCost,
            finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
            finishLoadWordCost]
          simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
          rw [hbaseAddresses]
        have hsuffixGas : suffixPre.gasLeft = (G + spare) +
            pauseDurationSavePauseCost suffixPre duration target
              previousPauser removedIndex arrayLength lastTarget := by
          simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
        rcases pauseDuration_save_pause_runCompiledTo
            (pre := suffixPre) (G := G + spare) (img := img)
            (stack := stack) (duration := duration)
            (previousPauser := previousPauser) (countValue := countValue)
            (decrementedCount := decrementedCount) (target := target)
            (arrayLength := arrayLength)
            (decrementedLength := decrementedLength)
            (removedIndex := removedIndex) (lastTarget := lastTarget)
            rfl hwf hr hdataTarget hsuffixDuration htargetNonzero
            htargetCanonical hsuffixAssignment hpreviousNonzero
            hpreviousCanonical hsuffixCount hcountSub harrayLengthBound
            hsuffixIndex hsuffixLength hdecrement hsuffixLast
            hlastCanonical hsuffixCode hsuffixAccess hsuffixWarmHole
            hsuffixWarmMoved hroom hstatic hemptyLookup hpauseLookup
            hfinishLookup hremoveLookup hafterLookup hsetPauserLookup
            hsuffixGas with
          ⟨raw, suffixRun, rawOutput, suffixPath⟩
        have hbranchRoom : branchPre.stack.length < 1024 := by
          simp only [branchPre, Devm.stack_setMach, List.length_cons]
          omega
        have hbranchGas : branchPre.gasLeft =
            suffixPre.gasLeft + branchCost := by
          simp only [branchPre, suffixPre, Devm.gasLeft_setMach]
          dsimp only [branchGas]
          omega
        have hbranchPop : Devm.PopBurnBy [1] branchCost branchPre
            suffixPre := by
          convert Devm.popBurnBy_setMach (devm := branchPre)
            (x := (1 : B256)) (s := stack) rfl hbranchGas using 1
          all_goals rfl
        let branchRun : Func.RunCompiledTo fs sevm branchPre
            ((pushB256 pauseDurationSlot ::: sload :::
              mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
              pushB256 0 ::: mstoreAt newPauserWord +++
              pushB256 0 ::: mstoreAt previousPauserWord +++
              pushB256 1 ::: mstoreAt continuationWord +++
              .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot))
            (.error (.revert, raw)) :=
          .succ (by decide) hbranchRoom hbranchPop suffixRun
        have branchPath : Func.RunCompiledTo.DirectPausePath
            sevm.currentTarget target (phase := .beforeWrite) branchRun :=
          .succ (nonzero := by decide) (room := hbranchRoom)
            (pop := hbranchPop) (tail := suffixRun) suffixPath
        have hlt : Ninst.RunCompiled sevm ltPre lt branchPre := by
          exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by
            simp [B256.ltCheck, hlive]) (by
              simp only [ltPre, Devm.gasLeft_setMach]
              dsimp only [ltGas]
              omega) (by omega)
        rcases directPausePath_prepend_childless
            (ca := sevm.currentTarget) (target := target) hlt (by simp)
            branchRun branchPath with ⟨ltRun, ltPath⟩
        have htimestamp : Ninst.RunCompiled sevm timestampPre timestamp
            ltPre := by
          have htimestampGas : timestampPre.gasLeft =
              (spare + ltGas) + gBase := by
            simp only [timestampPre, Devm.gasLeft_setMach, htailGas]
            dsimp only [timestampGas]
            omega
          simpa only [timestampPre, ltPre, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using
            Ninst.runCompiled_pushItem (sevm := sevm)
              (devm := timestampPre) (r := .timestamp)
              (x := sevm.benvStat.time) (cost := gBase)
              (G := spare + ltGas) (by rintro ⟨⟩) rfl
              htimestampGas (by
                simp only [timestampPre, Devm.stack_setMach,
                  List.length_cons]
                omega)
        rcases directPausePath_prepend_childless
            (ca := sevm.currentTarget) (target := target) htimestamp
            (by simp) (by simpa only [timestampPre, ltPre,
              Devm.setMach_setMach, Devm.stack_setMach,
              Devm.memory_setMach] using ltRun)
            (by simpa only [timestampPre, ltPre, Devm.setMach_setMach,
              Devm.stack_setMach,
              Devm.memory_setMach] using ltPath) with
          ⟨timestampRun, timestampPath⟩
        exact ⟨raw,
          by simpa only [timestampPre, htailGas, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using timestampRun,
          rawOutput,
          by simpa only [timestampPre, htailGas, Devm.setMach_setMach,
              Devm.stack_setMach,
              Devm.memory_setMach] using timestampPath⟩) with
    ⟨raw, sloadRun, rawOutput, sloadPath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (base := pre) (region := expiryRegion)
      (x := pauser) (stack := stack) (pushGas := tagPushCost)
      (G := sloadGas) rfl (by omega)
      (by simpa only [sloadPre, expirySlot, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using sloadRun)
      (by simpa only [sloadPre, expirySlot, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using sloadPath) with
    ⟨tagRun, tagPath⟩
  have hcallerGas : pre.gasLeft = tagGas + gBase := by
    rw [hgas]
    dsimp only [liveExpiryPauseCost, suffixCost, branchCost, tagPushCost,
      branchGas, ltGas, timestampGas, sloadGas, tagGas]
    omega
  have hcallerRun : Ninst.RunCompiled sevm pre caller
      (pre.setMach ⟨pauser :: stack, pre.memory, tagGas⟩) := by
    simpa only [hstack, hcaller] using Ninst.runCompiled_pushItem
      (sevm := sevm) (devm := pre) (r := .caller)
      (x := sevm.caller.toB256) (cost := gBase) (G := tagGas)
      (by rintro ⟨⟩) rfl hcallerGas (by rw [hstack]; omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hcallerRun (by simp)
      (by simpa only [tagGas, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [tagGas, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [prepend] using run,
    rawOutput,
    by simpa only [prepend] using path⟩

/-- Worst-case reserved cost of authorization followed by the live-expiry
pause path. -/
private def authorizedLiveExpiryPauseCost
    (pre : Devm) (duration target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  pushCost (4 : B256).toBytes.sig + gVerylow +
    pushCost (regionWord assignmentRegion).toBytes.sig + gVerylow +
    gasColdSload + gBase + gVerylow +
    (gVerylow + gHigh + gJumpdest) +
    liveExpiryPauseCost pre duration target previousPauser removedIndex
      arrayLength lastTarget

/- The concrete assignment authorizes the concrete caller, so equality yields
one and selects the textual live-expiry branch.  The untaken sender error needs
no lookup premise. -/
private theorem authorized_liveExpiry_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {pauser expiry duration previousPauser countValue decrementedCount target
      arrayLength decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + authorizedLiveExpiryPauseCost pre duration
      target previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (arg 0 +++ tagTop assignmentRegion +++ sload ::: caller ::: eq :::
          ((caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
            ((pushB256 pauseDurationSlot ::: sload :::
              mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
              pushB256 0 ::: mstoreAt newPauserWord +++
              pushB256 0 ::: mstoreAt previousPauserWord +++
              pushB256 1 ::: mstoreAt continuationWord +++
              .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot))) <?>
            (.call senderNotPauserErrorSlot)))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  have _hpauserFacts : pauser ≠ 0 ∧ canonicalAddress pauser :=
    ⟨hpauserNonzero, hpauserCanonical⟩
  let suffixCost := liveExpiryPauseCost pre duration target previousPauser
    removedIndex arrayLength lastTarget
  let branchCost := gVerylow + gHigh + gJumpdest
  let tagPushCost := pushCost (regionWord assignmentRegion).toBytes.sig
  let branchGas := G + suffixCost + branchCost
  let eqGas := branchGas + gVerylow
  let callerGas := eqGas + gBase
  let sloadGas := callerGas + gasColdSload
  let tagGas := sloadGas + gVerylow + tagPushCost
  let sloadPre := pre.setMach
    ⟨assignmentSlot target :: stack, pre.memory, sloadGas⟩
  have hsloadStack : sloadPre.stack = assignmentSlot target :: stack := rfl
  have hsloadValue : sloadPre.getStorVal sevm.currentTarget
      (assignmentSlot target) = pauser := by
    exact hauthorizationStorage
  have hsloadMemory : sloadPre.memory = pre.memory := rfl
  have hsloadGas : gasColdSload ≤ sloadPre.gasLeft := by
    simp only [sloadPre, Devm.gasLeft_setMach]
    dsimp only [sloadGas, callerGas, eqGas, branchGas]
    omega
  rcases directPausePath_sload_revert_step
      (fs := fs) (sevm := sevm) (ca := sevm.currentTarget)
      (target := target) (phase := .beforeWrite) (devm := sloadPre)
      (k := assignmentSlot target) (v := pauser) (s := stack)
      (M := pre.memory)
      (rest := caller ::: eq :::
        ((caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
          ((pushB256 pauseDurationSlot ::: sload :::
            mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
            pushB256 0 ::: mstoreAt newPauserWord +++
            pushB256 0 ::: mstoreAt previousPauserWord +++
            pushB256 1 ::: mstoreAt continuationWord +++
            .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot))) <?>
          (.call senderNotPauserErrorSlot)))
      hsloadStack (by omega) hsloadValue hsloadMemory hsloadGas (by
        intro base c sloadTailGas hkeyAccess haccessSubset hstorage hbalances
          hcode haddresses hrefund hlogs hlower hupper hgasEq
        let spare := gasColdSload - c
        have htailGas : sloadTailGas = callerGas + spare := by
          dsimp only [sloadPre, sloadGas] at hgasEq
          simp only [Devm.gasLeft_setMach] at hgasEq
          dsimp only [spare]
          omega
        let suffixPre := base.setMach
          ⟨stack, pre.memory, G + spare + suffixCost⟩
        let branchPre := base.setMach
          ⟨1 :: stack, pre.memory, spare + branchGas⟩
        let eqPre := base.setMach
          ⟨pauser :: pauser :: stack, pre.memory, spare + eqGas⟩
        let callerPre := base.setMach
          ⟨pauser :: stack, pre.memory, sloadTailGas⟩
        have hsuffixExpiry : suffixPre.getStorVal sevm.currentTarget
            (expirySlot pauser) = expiry := by
          change base.getStorVal sevm.currentTarget (expirySlot pauser) =
            expiry
          rw [hstorage]
          exact hexpiryStorage
        have hsuffixDuration : suffixPre.getStorVal sevm.currentTarget
            pauseDurationSlot = duration := by
          change base.getStorVal sevm.currentTarget pauseDurationSlot =
            duration
          rw [hstorage]
          exact hdurationStorage
        have hsuffixAssignment : suffixPre.getStorVal sevm.currentTarget
            (assignmentSlot target) = previousPauser := by
          change base.getStorVal sevm.currentTarget
            (assignmentSlot target) = previousPauser
          rw [hstorage]
          exact hassignmentStorage
        have hsuffixCount : suffixPre.getStorVal sevm.currentTarget
            (countSlot previousPauser) = countValue := by
          change base.getStorVal sevm.currentTarget
            (countSlot previousPauser) = countValue
          rw [hstorage]
          exact hcountStorage
        have hsuffixIndex : suffixPre.getStorVal sevm.currentTarget
            (indexSlot target) = removedIndex := by
          change base.getStorVal sevm.currentTarget (indexSlot target) =
            removedIndex
          rw [hstorage]
          exact hindexStorage
        have hsuffixLength : suffixPre.getStorVal sevm.currentTarget
            arrayLengthSlot = arrayLength := by
          change base.getStorVal sevm.currentTarget arrayLengthSlot =
            arrayLength
          rw [hstorage]
          exact hlengthStorage
        have hsuffixLast : suffixPre.getStorVal sevm.currentTarget
            (arrayEntrySlot arrayLength) = lastTarget := by
          change base.getStorVal sevm.currentTarget
            (arrayEntrySlot arrayLength) = lastTarget
          rw [hstorage]
          exact hlastStorage
        have hsuffixCode : (suffixPre.getCode target.toAdr).size = 0 := by
          change (base.getCode target.toAdr).size = 0
          rw [hcode target.toAdr]
          exact hcodeSize
        have hsuffixAccess : target.toAdr ∈ suffixPre.accessedAddresses ∨
            target.toAdr ∉ suffixPre.accessedAddresses := by
          change target.toAdr ∈ base.accessedAddresses ∨
            target.toAdr ∉ base.accessedAddresses
          rw [haddresses]
          exact haccess
        have hsuffixWarmHole :
            (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ :
              Adr × B256) ∈ suffixPre.accessedStorageKeys := by
          exact haccessSubset _ hwarmHole
        have hsuffixWarmMoved :
            (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
              suffixPre.accessedStorageKeys := by
          exact haccessSubset _ hwarmMovedIndex
        have haccessSetMach (d : Devm) (s' : List B256)
            (m' : Mem) (g' : Nat) :
            (d.setMach ⟨s', m', g'⟩).accessedAddresses =
              d.accessedAddresses := rfl
        have hbaseAddresses :
            base.accessedAddresses = pre.accessedAddresses := by
          exact haddresses
        have hsuffixCostEq : liveExpiryPauseCost suffixPre duration target
            previousPauser removedIndex arrayLength lastTarget =
              suffixCost := by
          dsimp only [suffixCost, suffixPre, liveExpiryPauseCost,
            pauseDurationSavePauseCost, targetArgSavePauseCost,
            newZeroPreviousContinuationKernelCallPauseCost,
            previousZeroContinuationKernelCallPauseCost,
            continuationSaveKernelCallPauseCost,
            setPauserKernelSingletonRemovalPauseCost,
            previousAssignmentSavePauseCost, assignmentZeroPauseCost,
            postAssignmentDecrementPauseCost,
            previousCountDecrementPauseCost, afterOldPauserPauseCost,
            removeTargetPauseCost, removeTargetLengthSavePauseCost,
            removeTargetLastSavePauseCost, removeTargetHolePauseCost,
            removeTargetMovedIndexPauseCost,
            removeTargetTailClearPauseCost, removeTargetLengthPauseCost,
            removeTargetFinalPauseCost, finishSetPauserPauseCost,
            finishSetPauserPauseSuffixCost,
            finishSetPauserPauseTerminalCost,
            finishSetPauserPauseBranchCost,
            finishSetPauserPauseCallCost, pauseAfterSetZeroCodeCost,
            finishLoadWordCost]
          simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
          rw [hbaseAddresses]
        have hsuffixGas : suffixPre.gasLeft = (G + spare) +
            liveExpiryPauseCost suffixPre duration target previousPauser
              removedIndex arrayLength lastTarget := by
          simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
        rcases liveExpiry_pause_runCompiledTo
            (pre := suffixPre) (G := G + spare) (img := img)
            (stack := stack) (pauser := pauser) (expiry := expiry)
            (duration := duration) (previousPauser := previousPauser)
            (countValue := countValue) (decrementedCount := decrementedCount)
            (target := target) (arrayLength := arrayLength)
            (decrementedLength := decrementedLength)
            (removedIndex := removedIndex) (lastTarget := lastTarget)
            rfl hwf hr hcaller hsuffixExpiry hlive hdataTarget
            hsuffixDuration htargetNonzero htargetCanonical
            hsuffixAssignment hpreviousNonzero hpreviousCanonical
            hsuffixCount hcountSub harrayLengthBound hsuffixIndex
            hsuffixLength hdecrement hsuffixLast hlastCanonical hsuffixCode
            hsuffixAccess hsuffixWarmHole hsuffixWarmMoved hroom hstatic
            hemptyLookup hpauseLookup hfinishLookup hremoveLookup
            hafterLookup hsetPauserLookup hsuffixGas with
          ⟨raw, suffixRun, rawOutput, suffixPath⟩
        have hbranchRoom : branchPre.stack.length < 1024 := by
          simp only [branchPre, Devm.stack_setMach, List.length_cons]
          omega
        have hbranchGas : branchPre.gasLeft =
            suffixPre.gasLeft + branchCost := by
          simp only [branchPre, suffixPre, Devm.gasLeft_setMach]
          dsimp only [branchGas]
          omega
        have hbranchPop : Devm.PopBurnBy [1] branchCost branchPre
            suffixPre := by
          convert Devm.popBurnBy_setMach (devm := branchPre)
            (x := (1 : B256)) (s := stack) rfl hbranchGas using 1
          all_goals rfl
        let branchRun : Func.RunCompiledTo fs sevm branchPre
            ((caller ::: tagTop expiryRegion +++ sload ::: timestamp :::
              lt ::: ((pushB256 pauseDurationSlot ::: sload :::
                mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
                pushB256 0 ::: mstoreAt newPauserWord +++
                pushB256 0 ::: mstoreAt previousPauserWord +++
                pushB256 1 ::: mstoreAt continuationWord +++
                .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot)))
              <?> (.call senderNotPauserErrorSlot))
            (.error (.revert, raw)) :=
          .succ (by decide) hbranchRoom hbranchPop suffixRun
        have branchPath : Func.RunCompiledTo.DirectPausePath
            sevm.currentTarget target (phase := .beforeWrite) branchRun :=
          .succ (nonzero := by decide) (room := hbranchRoom)
            (pop := hbranchPop) (tail := suffixRun) suffixPath
        have heq : Ninst.RunCompiled sevm eqPre eq branchPre := by
          exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by
            simp [B256.eqCheck]) (by
              simp only [eqPre, Devm.gasLeft_setMach]
              dsimp only [eqGas]
              omega) (by omega)
        rcases directPausePath_prepend_childless
            (ca := sevm.currentTarget) (target := target) heq (by simp)
            branchRun branchPath with ⟨eqRun, eqPath⟩
        have hcallerRun : Ninst.RunCompiled sevm callerPre caller eqPre := by
          have hcallerGas : callerPre.gasLeft =
              (spare + eqGas) + gBase := by
            simp only [callerPre, Devm.gasLeft_setMach, htailGas]
            dsimp only [callerGas]
            omega
          simpa only [callerPre, eqPre, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach, hcaller] using
            Ninst.runCompiled_pushItem (sevm := sevm) (devm := callerPre)
              (r := .caller) (x := sevm.caller.toB256) (cost := gBase)
              (G := spare + eqGas) (by rintro ⟨⟩) rfl hcallerGas (by
                simp only [callerPre, Devm.stack_setMach,
                  List.length_cons]
                omega)
        rcases directPausePath_prepend_childless
            (ca := sevm.currentTarget) (target := target) hcallerRun
            (by simp) (by simpa only [callerPre, eqPre,
              Devm.setMach_setMach, Devm.stack_setMach,
              Devm.memory_setMach] using eqRun)
            (by simpa only [callerPre, eqPre, Devm.setMach_setMach,
              Devm.stack_setMach,
              Devm.memory_setMach] using eqPath) with
          ⟨callerRun, callerPath⟩
        exact ⟨raw,
          by simpa only [callerPre, htailGas, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using callerRun,
          rawOutput,
          by simpa only [callerPre, htailGas, Devm.setMach_setMach,
              Devm.stack_setMach,
              Devm.memory_setMach] using callerPath⟩) with
    ⟨raw, sloadRun, rawOutput, sloadPath⟩
  rcases directPausePath_prepend_tagTop
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (base := pre) (region := assignmentRegion)
      (x := target) (stack := stack) (pushGas := tagPushCost)
      (G := sloadGas) rfl (by omega)
      (by simpa only [sloadPre, assignmentSlot, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using sloadRun)
      (by simpa only [sloadPre, assignmentSlot, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using sloadPath) with
    ⟨tagRun, tagPath⟩
  have hargGas : pre.gasLeft =
      tagGas + gVerylow + pushCost (4 : B256).toBytes.sig := by
    rw [hgas]
    dsimp only [authorizedLiveExpiryPauseCost, suffixCost, branchCost,
      tagPushCost, branchGas, eqGas, callerGas, sloadGas, tagGas]
    omega
  rcases directPausePath_prepend_arg_zero
      (pre := pre) (value := target) (markedTarget := target)
      (stack := stack) (G := tagGas) (phase := .beforeWrite)
      hstack hdataTarget hargGas (by omega)
      (by simpa only [tagGas, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagRun)
      (by simpa only [tagGas, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tagPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [prepend] using run,
    rawOutput,
    by simpa only [prepend] using path⟩

/-- Exact phase-preserving `TLOAD` prepend. -/
private theorem directPausePath_prepend_tload
    {ca : Adr} {target key value : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {stack : List B256} {G : Nat} {body : Func} {out : Execution}
    (hstack : pre.stack = key :: stack)
    (hvalue : pre.getTransVal sevm.currentTarget key = value)
    (hgas : pre.gasLeft = G + gasWarmAccess)
    (hroom : stack.length < 1024)
    (tail : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨value :: stack, pre.memory, G⟩) body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca target
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (tload ::: body) out,
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run := by
  have hcore : Rinst.runCore 0 pre sevm .tload =
      .ok (pre.setMach ⟨value :: stack, pre.memory, G⟩) := by
    show (do
      let ⟨k, d⟩ ← pre.pop
      pushItem (d.getTransVal sevm.currentTarget k) gasWarmAccess d) = _
    rw [Devm.pop_eq_ok hstack]
    simp only [bind, Except.bind]
    rw [show (pre.setMach
      ⟨stack, pre.memory, pre.gasLeft⟩).getTransVal
        sevm.currentTarget key = value by exact hvalue]
    rw [pushItem_eq_ok (by
      simp only [Devm.gasLeft_setMach]
      omega) (by
      simp only [Devm.stack_setMach]
      exact hroom)]
    simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach, Devm.gasLeft_setMach]
    rw [show pre.gasLeft - gasWarmAccess = G by omega]
  have instructionRun : Ninst.RunCompiled sevm pre tload
      (pre.setMach ⟨value :: stack, pre.memory, G⟩) :=
    Ninst.runCompiled_reg (by rintro ⟨⟩) hcore
  exact directPausePath_prepend_childless
    (ca := ca) (target := target) instructionRun (by simp) tail tailPath

/-- Exact phase-preserving `TSTORE` prepend.  The machine pops the key first,
then its new value. -/
private theorem directPausePath_prepend_tstore
    {ca : Adr} {target key value : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {stack : List B256} {G : Nat} {body : Func} {out : Execution}
    (hstack : pre.stack = key :: value :: stack)
    (hstatic : sevm.isStatic = false)
    (hgas : pre.gasLeft = G + gasWarmAccess)
    (tail : Func.RunCompiledTo fs sevm
      ((pre.setMach ⟨stack, pre.memory, G⟩).setTransVal
        sevm.currentTarget key value) body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca target
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (tstore ::: body) out,
      Func.RunCompiledTo.DirectPausePath ca target
        (phase := phase) run := by
  have hcore : Rinst.runCore 0 pre sevm .tstore =
      .ok ((pre.setMach ⟨stack, pre.memory, G⟩).setTransVal
        sevm.currentTarget key value) := by
    show (do
      let ⟨k, d⟩ ← pre.pop
      let ⟨v, d⟩ ← d.pop
      let d ← chargeGas gasWarmAccess d
      assertDynamic sevm d
      .ok (d.setTransVal sevm.currentTarget k v)) = _
    rw [Devm.pop_eq_ok hstack]
    simp only [bind, Except.bind]
    rw [Devm.pop_eq_ok
      (devm := pre.setMach
        ⟨value :: stack, pre.memory, pre.gasLeft⟩) rfl]
    simp only [Devm.setMach_setMach, Devm.memory_setMach,
      Devm.gasLeft_setMach]
    rw [chargeGas_eq_ok
      (devm := pre.setMach ⟨stack, pre.memory, pre.gasLeft⟩) (by
        simp only [Devm.gasLeft_setMach]
        omega)]
    have hremaining : pre.gasLeft - gasWarmAccess = G := by omega
    simp only [Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
    rw [hremaining]
    simp [assertDynamic, Except.assert, hstatic]
  have instructionRun : Ninst.RunCompiled sevm pre tstore
      ((pre.setMach ⟨stack, pre.memory, G⟩).setTransVal
        sevm.currentTarget key value) :=
    Ninst.runCompiled_reg (by rintro ⟨⟩) hcore
  exact directPausePath_prepend_childless
    (ca := ca) (target := target) instructionRun (by simp) tail tailPath

/-- Exact cost of taking the pause lock before the authorized live-expiry
path. -/
private def lockWriteAuthorizedPauseCost
    (pre : Devm) (duration target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  pushCost (1 : B256).toBytes.sig + pushCost lockKey.toBytes.sig +
    gasWarmAccess + authorizedLiveExpiryPauseCost pre duration target
      previousPauser removedIndex arrayLength lastTarget

/-- The accumulated authorization/live-expiry cost depends on the machine
state only through memory and the warm account set. -/
private theorem authorizedLiveExpiryPauseCost_eq_of_memory_accessed
    {left right : Devm}
    (hmemory : left.memory = right.memory)
    (haccessed : left.accessedAddresses = right.accessedAddresses)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) :
    authorizedLiveExpiryPauseCost left duration target previousPauser
        removedIndex arrayLength lastTarget =
      authorizedLiveExpiryPauseCost right duration target previousPauser
        removedIndex arrayLength lastTarget := by
  have haccessSetMach (d : Devm) (s' : List B256)
      (m' : Mem) (g' : Nat) :
      (d.setMach ⟨s', m', g'⟩).accessedAddresses = d.accessedAddresses := rfl
  dsimp only [authorizedLiveExpiryPauseCost, liveExpiryPauseCost,
    pauseDurationSavePauseCost, targetArgSavePauseCost,
    newZeroPreviousContinuationKernelCallPauseCost,
    previousZeroContinuationKernelCallPauseCost,
    continuationSaveKernelCallPauseCost,
    setPauserKernelSingletonRemovalPauseCost,
    previousAssignmentSavePauseCost, assignmentZeroPauseCost,
    postAssignmentDecrementPauseCost, previousCountDecrementPauseCost,
    afterOldPauserPauseCost, removeTargetPauseCost,
    removeTargetLengthSavePauseCost, removeTargetLastSavePauseCost,
    removeTargetHolePauseCost, removeTargetMovedIndexPauseCost,
    removeTargetTailClearPauseCost, removeTargetLengthPauseCost,
    removeTargetFinalPauseCost, finishSetPauserPauseCost,
    finishSetPauserPauseSuffixCost, finishSetPauserPauseTerminalCost,
    finishSetPauserPauseBranchCost, finishSetPauserPauseCallCost,
    pauseAfterSetZeroCodeCost, finishLoadWordCost]
  simp only [Devm.memory_setMach, Devm.extCost, haccessSetMach]
  rw [hmemory, haccessed]

/- Set the transient pause lock and execute the authorized live-expiry path.
Only transient storage changes before the persistent Registry path begins. -/
private theorem lock_write_authorized_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {pauser expiry duration previousPauser countValue decrementedCount target
      arrayLength decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + lockWriteAuthorizedPauseCost pre duration
      target previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 1 ::: pushB256 lockKey ::: tstore :::
          arg 0 +++ tagTop assignmentRegion +++ sload ::: caller ::: eq :::
          ((caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
            ((pushB256 pauseDurationSlot ::: sload :::
              mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
              pushB256 0 ::: mstoreAt newPauserWord +++
              pushB256 0 ::: mstoreAt previousPauserWord +++
              pushB256 1 ::: mstoreAt continuationWord +++
              .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot))) <?>
            (.call senderNotPauserErrorSlot)))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let suffixCost := authorizedLiveExpiryPauseCost pre duration target
    previousPauser removedIndex arrayLength lastTarget
  let onePushCost := pushCost (1 : B256).toBytes.sig
  let keyPushCost := pushCost lockKey.toBytes.sig
  let storeGas := G + suffixCost + gasWarmAccess
  let keyPushGas := storeGas + keyPushCost
  let storePre := pre.setMach
    ⟨lockKey :: 1 :: stack, pre.memory, storeGas⟩
  let locked := (pre.setMach
    ⟨stack, pre.memory, G + suffixCost⟩).setTransVal
      sevm.currentTarget lockKey 1
  have hlockedWf : Mem.Wf locked.memory := by
    exact hwf
  have hlockedReads : Mem.Reads locked.memory img := by
    exact hr
  have hlockedAuthorization : locked.getStorVal sevm.currentTarget
      (assignmentSlot target) = pauser := by
    exact hauthorizationStorage
  have hlockedExpiry : locked.getStorVal sevm.currentTarget
      (expirySlot pauser) = expiry := by
    exact hexpiryStorage
  have hlockedDuration : locked.getStorVal sevm.currentTarget
      pauseDurationSlot = duration := by
    exact hdurationStorage
  have hlockedAssignment : locked.getStorVal sevm.currentTarget
      (assignmentSlot target) = previousPauser := by
    exact hassignmentStorage
  have hlockedCount : locked.getStorVal sevm.currentTarget
      (countSlot previousPauser) = countValue := by
    exact hcountStorage
  have hlockedIndex : locked.getStorVal sevm.currentTarget
      (indexSlot target) = removedIndex := by
    exact hindexStorage
  have hlockedLength : locked.getStorVal sevm.currentTarget
      arrayLengthSlot = arrayLength := by
    exact hlengthStorage
  have hlockedLast : locked.getStorVal sevm.currentTarget
      (arrayEntrySlot arrayLength) = lastTarget := by
    exact hlastStorage
  have hlockedCode : (locked.getCode target.toAdr).size = 0 := by
    exact hcodeSize
  have hlockedAccess : target.toAdr ∈ locked.accessedAddresses ∨
      target.toAdr ∉ locked.accessedAddresses := by
    exact haccess
  have hlockedWarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        locked.accessedStorageKeys := by
    exact hwarmHole
  have hlockedWarmMoved :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        locked.accessedStorageKeys := by
    exact hwarmMovedIndex
  have hlockedCostEq : authorizedLiveExpiryPauseCost locked duration target
      previousPauser removedIndex arrayLength lastTarget = suffixCost := by
    change authorizedLiveExpiryPauseCost locked duration target
      previousPauser removedIndex arrayLength lastTarget =
        authorizedLiveExpiryPauseCost pre duration target previousPauser
          removedIndex arrayLength lastTarget
    exact authorizedLiveExpiryPauseCost_eq_of_memory_accessed
      (left := locked) (right := pre) rfl rfl duration target previousPauser
      removedIndex arrayLength lastTarget
  have hlockedGas : locked.gasLeft = G +
      authorizedLiveExpiryPauseCost locked duration target previousPauser
        removedIndex arrayLength lastTarget := by
    rw [hlockedCostEq]
    rfl
  rcases authorized_liveExpiry_pause_runCompiledTo
      (pre := locked) (G := G) (img := img) (stack := stack)
      (pauser := pauser) (expiry := expiry) (duration := duration)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hlockedWf hlockedReads hdataTarget hcaller hpauserNonzero
      hpauserCanonical hlockedAuthorization hlockedExpiry hlive
      hlockedDuration htargetNonzero htargetCanonical hlockedAssignment
      hpreviousNonzero hpreviousCanonical hlockedCount hcountSub
      harrayLengthBound hlockedIndex hlockedLength hdecrement hlockedLast
      hlastCanonical hlockedCode hlockedAccess hlockedWarmHole
      hlockedWarmMoved hroom hstatic hemptyLookup hpauseLookup
      hfinishLookup hremoveLookup hafterLookup hsetPauserLookup hlockedGas with
    ⟨raw, tail, rawOutput, tailPath⟩
  have hstoreStack : storePre.stack = lockKey :: 1 :: stack := rfl
  have hstoreGas : storePre.gasLeft =
      (G + suffixCost) + gasWarmAccess := by
    simp only [storePre, Devm.gasLeft_setMach]
    dsimp only [storeGas]
  rcases directPausePath_prepend_tstore
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := storePre) (key := lockKey)
      (value := 1) (stack := stack) (G := G + suffixCost)
      hstoreStack hstatic hstoreGas
      (by simpa only [locked, storePre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using tail)
      (by simpa only [locked, storePre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach] using tailPath) with
    ⟨storeRun, storePath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite)
      (pre := pre.setMach
        ⟨1 :: stack, pre.memory, keyPushGas⟩)
      (word := lockKey) (stack := 1 :: stack) (c := keyPushCost)
      (G := storeGas) rfl rfl rfl
      (by simp only [List.length_cons]; omega)
      (by simpa only [storePre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using storeRun)
      (by simpa only [storePre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using storePath) with
    ⟨keyRun, keyPath⟩
  have honeGas : pre.gasLeft = keyPushGas + onePushCost := by
    rw [hgas]
    dsimp only [lockWriteAuthorizedPauseCost, suffixCost, onePushCost,
      keyPushCost, storeGas, keyPushGas]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pre) (word := 1) (stack := stack)
      (c := onePushCost) (G := keyPushGas) hstack rfl honeGas (by omega)
      (by simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using keyRun)
      (by simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using keyPath) with
    ⟨run, path⟩
  exact ⟨raw, run, rawOutput, path⟩

/-- Worst-case reserved cost of reading the transient lock, selecting the
unlocked branch, and executing the complete lock-write pause path. -/
private def unlockedGuardPauseCost
    (pre : Devm) (duration target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  pushCost lockKey.toBytes.sig + gasWarmAccess + gVerylow +
    (gVerylow + gHigh + gJumpdest) +
    lockWriteAuthorizedPauseCost pre duration target previousPauser
      removedIndex arrayLength lastTarget

/- A zero transient lock maps through `ISZERO` to one and selects the textual
lock-write branch.  The untaken reentrant error needs no lookup premise. -/
private theorem unlocked_guard_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {pauser expiry duration previousPauser countValue decrementedCount target
      arrayLength decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + unlockedGuardPauseCost pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (pushB256 lockKey ::: tload ::: iszero :::
          ((pushB256 1 ::: pushB256 lockKey ::: tstore :::
            arg 0 +++ tagTop assignmentRegion +++ sload ::: caller ::: eq :::
            ((caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
              ((pushB256 pauseDurationSlot ::: sload :::
                mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
                pushB256 0 ::: mstoreAt newPauserWord +++
                pushB256 0 ::: mstoreAt previousPauserWord +++
                pushB256 1 ::: mstoreAt continuationWord +++
                .call setPauserSlot) <?>
                  (.call heartbeatExpiredErrorSlot))) <?>
              (.call senderNotPauserErrorSlot))) <?>
            (.call reentrantCallErrorSlot)))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let suffixCost := lockWriteAuthorizedPauseCost pre duration target
    previousPauser removedIndex arrayLength lastTarget
  let branchCost := gVerylow + gHigh + gJumpdest
  let keyPushCost := pushCost lockKey.toBytes.sig
  let branchGas := G + suffixCost + branchCost
  let iszeroGas := branchGas + gVerylow
  let tloadGas := iszeroGas + gasWarmAccess
  let suffixPre := pre.setMach ⟨stack, pre.memory, G + suffixCost⟩
  let branchPre := pre.setMach ⟨1 :: stack, pre.memory, branchGas⟩
  let iszeroPre := pre.setMach ⟨0 :: stack, pre.memory, iszeroGas⟩
  let tloadPre := pre.setMach ⟨lockKey :: stack, pre.memory, tloadGas⟩
  have hsuffixCostEq : lockWriteAuthorizedPauseCost suffixPre duration target
      previousPauser removedIndex arrayLength lastTarget = suffixCost := by
    change pushCost (1 : B256).toBytes.sig + pushCost lockKey.toBytes.sig +
        gasWarmAccess +
          authorizedLiveExpiryPauseCost suffixPre duration target
            previousPauser removedIndex arrayLength lastTarget =
      pushCost (1 : B256).toBytes.sig + pushCost lockKey.toBytes.sig +
        gasWarmAccess +
          authorizedLiveExpiryPauseCost pre duration target previousPauser
            removedIndex arrayLength lastTarget
    rw [authorizedLiveExpiryPauseCost_eq_of_memory_accessed
      (left := suffixPre) (right := pre) rfl rfl]
  have hsuffixGas : suffixPre.gasLeft = G +
      lockWriteAuthorizedPauseCost suffixPre duration target previousPauser
        removedIndex arrayLength lastTarget := by
    simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
  rcases lock_write_authorized_pause_runCompiledTo
      (pre := suffixPre) (G := G) (img := img) (stack := stack)
      (pauser := pauser) (expiry := expiry) (duration := duration)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwf hr hdataTarget hcaller hpauserNonzero hpauserCanonical
      hauthorizationStorage hexpiryStorage hlive hdurationStorage
      htargetNonzero htargetCanonical hassignmentStorage hpreviousNonzero
      hpreviousCanonical hcountStorage hcountSub harrayLengthBound
      hindexStorage hlengthStorage hdecrement hlastStorage hlastCanonical
      hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic
      hemptyLookup hpauseLookup hfinishLookup hremoveLookup hafterLookup
      hsetPauserLookup hsuffixGas with
    ⟨raw, suffixRun, rawOutput, suffixPath⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas : branchPre.gasLeft =
      suffixPre.gasLeft + branchCost := by
    simp only [branchPre, suffixPre, Devm.gasLeft_setMach]
    dsimp only [branchGas]
  have hbranchPop : Devm.PopBurnBy [1] branchCost branchPre suffixPre := by
    convert Devm.popBurnBy_setMach (devm := branchPre)
      (x := (1 : B256)) (s := stack) rfl hbranchGas using 1
    all_goals rfl
  let branchRun : Func.RunCompiledTo fs sevm branchPre
      ((pushB256 1 ::: pushB256 lockKey ::: tstore :::
        arg 0 +++ tagTop assignmentRegion +++ sload ::: caller ::: eq :::
        ((caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
          ((pushB256 pauseDurationSlot ::: sload :::
            mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
            pushB256 0 ::: mstoreAt newPauserWord +++
            pushB256 0 ::: mstoreAt previousPauserWord +++
            pushB256 1 ::: mstoreAt continuationWord +++
            .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot))) <?>
          (.call senderNotPauserErrorSlot))) <?>
        (.call reentrantCallErrorSlot))
      (.error (.revert, raw)) :=
    .succ (by decide) hbranchRoom hbranchPop suffixRun
  have branchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) branchRun :=
    .succ (nonzero := by decide) (room := hbranchRoom)
      (pop := hbranchPop) (tail := suffixRun) suffixPath
  have hiszero : Ninst.RunCompiled sevm iszeroPre iszero branchPre := by
    exact Ninst.runCompiled_unary (by rintro ⟨⟩) rfl rfl (by
      simp [B256.eqCheck]) (by
      simp only [iszeroPre, Devm.gasLeft_setMach]
      dsimp only [iszeroGas]) (by omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hiszero (by simp)
      branchRun branchPath with ⟨iszeroRun, iszeroPath⟩
  have htloadGas : tloadPre.gasLeft = iszeroGas + gasWarmAccess := by
    simp only [tloadPre, Devm.gasLeft_setMach]
    dsimp only [tloadGas]
  rcases directPausePath_prepend_tload
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := tloadPre) (key := lockKey)
      (value := 0) (stack := stack) (G := iszeroGas) rfl hlock htloadGas
      (by omega)
      (by simpa only [iszeroPre, tloadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using iszeroRun)
      (by simpa only [iszeroPre, tloadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using iszeroPath) with
    ⟨tloadRun, tloadPath⟩
  have hpushGas : pre.gasLeft = tloadGas + keyPushCost := by
    rw [hgas]
    dsimp only [unlockedGuardPauseCost, suffixCost, branchCost, keyPushCost,
      branchGas, iszeroGas, tloadGas]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pre) (word := lockKey)
      (stack := stack) (c := keyPushCost) (G := tloadGas)
      hstack rfl hpushGas (by omega)
      (by simpa only [tloadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tloadRun)
      (by simpa only [tloadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using tloadPath) with
    ⟨run, path⟩
  exact ⟨raw, run, rawOutput, path⟩

/-- Exact cost of the compact `pushAddressMask` sequence and its final AND. -/
private def checkNonAddressPauseCost : Nat :=
  pushCost (0 : B256).toBytes.sig + gVerylow +
    pushCost (Nat.toB256 160).toBytes.sig + gVerylow + gVerylow

/-- Phase-preserving construction of a successful `checkNonAddress`: the
explicit high-bit mask result is zero. -/
private theorem directPausePath_prepend_checkNonAddress_zero
    {ca : Adr} {markedTarget target : B256} {phase : DirectPausePhase}
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {stack : List B256} {G : Nat} {body : Func} {out : Execution}
    (hstack : pre.stack = target :: stack)
    (hmask : addressMask &&& target = 0)
    (hgas : pre.gasLeft = G + checkNonAddressPauseCost)
    (hroom : stack.length < 1022)
    (tail : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨0 :: stack, pre.memory, G⟩) body out)
    (tailPath : Func.RunCompiledTo.DirectPausePath ca markedTarget
      (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (checkNonAddress +++ body) out,
      Func.RunCompiledTo.DirectPausePath ca markedTarget
        (phase := phase) run := by
  let push160Cost := pushCost (Nat.toB256 160).toBytes.sig
  let pushZeroCost := pushCost (0 : B256).toBytes.sig
  let andPre := pre.setMach
    ⟨addressMask :: target :: stack, pre.memory, G + gVerylow⟩
  let shlPre := pre.setMach
    ⟨Nat.toB256 160 :: (~~~(0 : B256)) :: target :: stack, pre.memory,
      G + gVerylow + gVerylow⟩
  let push160Pre := pre.setMach
    ⟨(~~~(0 : B256)) :: target :: stack, pre.memory,
      G + gVerylow + gVerylow + push160Cost⟩
  let notPre := pre.setMach
    ⟨0 :: target :: stack, pre.memory,
      G + gVerylow + gVerylow + push160Cost + gVerylow⟩
  have hand : Ninst.RunCompiled sevm andPre (.reg .and)
      (pre.setMach ⟨0 :: stack, pre.memory, G⟩) := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl hmask (by
      simp only [andPre, Devm.gasLeft_setMach]) (by omega)
  rcases directPausePath_prepend_childless
      (ca := ca) (target := markedTarget) hand (by simp) tail tailPath with
    ⟨andRun, andPath⟩
  have hshl : Ninst.RunCompiled sevm shlPre (.reg .shl) andPre := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by
      simpa using addressMask_eq_shl.symm) (by
      simp only [shlPre, Devm.gasLeft_setMach]) (by
      simp only [List.length_cons]
      omega)
  rcases directPausePath_prepend_childless
      (ca := ca) (target := markedTarget) hshl (by simp)
      (by simpa only [shlPre, andPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using andRun)
      (by simpa only [shlPre, andPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using andPath) with
    ⟨shlRun, shlPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := ca) (target := markedTarget) (phase := phase)
      (pre := push160Pre) (word := Nat.toB256 160)
      (stack := (~~~(0 : B256)) :: target :: stack)
      (c := push160Cost) (G := G + gVerylow + gVerylow)
      rfl rfl rfl (by simp only [List.length_cons]; omega)
      (by simpa only [push160Pre, shlPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using shlRun)
      (by simpa only [push160Pre, shlPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using shlPath) with
    ⟨push160Run, push160Path⟩
  have hnot : Ninst.RunCompiled sevm notPre (.reg .not) push160Pre := by
    exact Ninst.runCompiled_unary (by rintro ⟨⟩) rfl rfl rfl (by
      simp only [notPre, Devm.gasLeft_setMach]) (by
      simp only [List.length_cons]
      omega)
  rcases directPausePath_prepend_childless
      (ca := ca) (target := markedTarget) hnot (by simp)
      (by simpa only [notPre, push160Pre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using push160Run)
      (by simpa only [notPre, push160Pre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using push160Path) with
    ⟨notRun, notPath⟩
  have hpushZeroGas : pre.gasLeft =
      (G + gVerylow + gVerylow + push160Cost + gVerylow) + pushZeroCost := by
    rw [hgas]
    dsimp only [checkNonAddressPauseCost, push160Cost, pushZeroCost]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := ca) (target := markedTarget) (phase := phase)
      (pre := pre) (word := 0) (stack := target :: stack)
      (c := pushZeroCost)
      (G := G + gVerylow + gVerylow + push160Cost + gVerylow)
      hstack rfl hpushZeroGas
      (by simp only [List.length_cons]; omega)
      (by simpa only [notPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using notRun)
      (by simpa only [notPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using notPath) with
    ⟨run, path⟩
  exact ⟨by simpa only [checkNonAddress, pushAddressMask, prepend,
      prepend_append] using run,
    by simpa only [checkNonAddress, pushAddressMask, prepend,
      prepend_append] using path⟩

/-- Exact cost of the canonical-address decoder wrapped around the unlocked
pause path. -/
private def canonicalUnlockedPauseCost
    (pre : Devm) (duration target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  pushCost (4 : B256).toBytes.sig + gVerylow +
    checkNonAddressPauseCost + (gVerylow + gHigh) +
    unlockedGuardPauseCost pre duration target previousPauser removedIndex
      arrayLength lastTarget

/- The canonical target has no high bits, so `canonicalAddressArg 0` selects
its textual body.  The untaken empty-revert call needs no lookup premise. -/
private theorem canonical_unlocked_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {pauser expiry duration previousPauser countValue decrementedCount target
      arrayLength decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + canonicalUnlockedPauseCost pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (canonicalAddressArg 0
          (pushB256 lockKey ::: tload ::: iszero :::
            ((pushB256 1 ::: pushB256 lockKey ::: tstore :::
              arg 0 +++ tagTop assignmentRegion +++ sload ::: caller :::
              eq ::: ((caller ::: tagTop expiryRegion +++ sload :::
                timestamp ::: lt :::
                ((pushB256 pauseDurationSlot ::: sload :::
                  mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
                  pushB256 0 ::: mstoreAt newPauserWord +++
                  pushB256 0 ::: mstoreAt previousPauserWord +++
                  pushB256 1 ::: mstoreAt continuationWord +++
                  .call setPauserSlot) <?>
                    (.call heartbeatExpiredErrorSlot))) <?>
                (.call senderNotPauserErrorSlot))) <?>
              (.call reentrantCallErrorSlot))))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let suffixCost := unlockedGuardPauseCost pre duration target previousPauser
    removedIndex arrayLength lastTarget
  let branchCost := gVerylow + gHigh
  let branchGas := G + suffixCost + branchCost
  let checkGas := branchGas + checkNonAddressPauseCost
  let suffixPre := pre.setMach ⟨stack, pre.memory, G + suffixCost⟩
  let branchPre := pre.setMach ⟨0 :: stack, pre.memory, branchGas⟩
  let checkPre := pre.setMach ⟨target :: stack, pre.memory, checkGas⟩
  have hsuffixCostEq : unlockedGuardPauseCost suffixPre duration target
      previousPauser removedIndex arrayLength lastTarget = suffixCost := by
    change pushCost lockKey.toBytes.sig + gasWarmAccess + gVerylow +
          (gVerylow + gHigh + gJumpdest) +
          (pushCost (1 : B256).toBytes.sig + pushCost lockKey.toBytes.sig +
            gasWarmAccess +
              authorizedLiveExpiryPauseCost suffixPre duration target
                previousPauser removedIndex arrayLength lastTarget) =
      pushCost lockKey.toBytes.sig + gasWarmAccess + gVerylow +
          (gVerylow + gHigh + gJumpdest) +
          (pushCost (1 : B256).toBytes.sig + pushCost lockKey.toBytes.sig +
            gasWarmAccess +
              authorizedLiveExpiryPauseCost pre duration target
                previousPauser removedIndex arrayLength lastTarget)
    rw [authorizedLiveExpiryPauseCost_eq_of_memory_accessed
      (left := suffixPre) (right := pre) rfl rfl]
  have hsuffixGas : suffixPre.gasLeft = G +
      unlockedGuardPauseCost suffixPre duration target previousPauser
        removedIndex arrayLength lastTarget := by
    simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
  rcases unlocked_guard_pause_runCompiledTo
      (pre := suffixPre) (G := G) (img := img) (stack := stack)
      (pauser := pauser) (expiry := expiry) (duration := duration)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwf hr hlock hdataTarget hcaller hpauserNonzero hpauserCanonical
      hauthorizationStorage hexpiryStorage hlive hdurationStorage
      htargetNonzero htargetCanonical hassignmentStorage hpreviousNonzero
      hpreviousCanonical hcountStorage hcountSub harrayLengthBound
      hindexStorage hlengthStorage hdecrement hlastStorage hlastCanonical
      hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic
      hemptyLookup hpauseLookup hfinishLookup hremoveLookup hafterLookup
      hsetPauserLookup hsuffixGas with
    ⟨raw, suffixRun, rawOutput, suffixPath⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas : branchPre.gasLeft =
      suffixPre.gasLeft + branchCost := by
    simp only [branchPre, suffixPre, Devm.gasLeft_setMach]
    dsimp only [branchGas]
  have hbranchPop : Devm.PopBurnBy [0] branchCost branchPre suffixPre := by
    convert Devm.popBurnBy_setMach (devm := branchPre)
      (x := (0 : B256)) (s := stack) rfl hbranchGas using 1
    all_goals rfl
  let branchRun : Func.RunCompiledTo fs sevm branchPre
      ((.call emptyRevertSlot) <?>
        (pushB256 lockKey ::: tload ::: iszero :::
          ((pushB256 1 ::: pushB256 lockKey ::: tstore :::
            arg 0 +++ tagTop assignmentRegion +++ sload ::: caller ::: eq :::
            ((caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
              ((pushB256 pauseDurationSlot ::: sload :::
                mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
                pushB256 0 ::: mstoreAt newPauserWord +++
                pushB256 0 ::: mstoreAt previousPauserWord +++
                pushB256 1 ::: mstoreAt continuationWord +++
                .call setPauserSlot) <?>
                  (.call heartbeatExpiredErrorSlot))) <?>
              (.call senderNotPauserErrorSlot))) <?>
            (.call reentrantCallErrorSlot))))
      (.error (.revert, raw)) :=
    .zero hbranchRoom hbranchPop suffixRun
  have branchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) branchRun :=
    .zero (room := hbranchRoom) (pop := hbranchPop)
      (tail := suffixRun) suffixPath
  have hcheckGas : checkPre.gasLeft =
      branchGas + checkNonAddressPauseCost := by
    simp only [checkPre, Devm.gasLeft_setMach]
    dsimp only [checkGas]
  rcases directPausePath_prepend_checkNonAddress_zero
      (ca := sevm.currentTarget) (markedTarget := target)
      (phase := .beforeWrite) (pre := checkPre) (target := target)
      (stack := stack) (G := branchGas) rfl hmask hcheckGas (by omega)
      (by simpa only [branchPre, checkPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using branchRun)
      (by simpa only [branchPre, checkPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using branchPath) with
    ⟨checkRun, checkPath⟩
  have hargGas : pre.gasLeft =
      checkGas + gVerylow + pushCost (4 : B256).toBytes.sig := by
    rw [hgas]
    dsimp only [canonicalUnlockedPauseCost, suffixCost, branchCost,
      branchGas, checkGas]
    omega
  rcases directPausePath_prepend_arg_zero
      (pre := pre) (value := target) (markedTarget := target)
      (stack := stack) (G := checkGas) (phase := .beforeWrite)
      hstack hdataTarget hargGas (by omega)
      (by simpa only [checkPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using checkRun)
      (by simpa only [checkPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using checkPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [canonicalAddressArg, prepend] using run,
    rawOutput,
    by simpa only [canonicalAddressArg, prepend] using path⟩

/-- Exact cost of the one-word static-calldata guard around the complete pause
path. -/
private def exactPauseCost
    (pre : Devm) (duration target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  pushCost (Nat.toB256 36).toBytes.sig + gBase + gVerylow +
    (gVerylow + gHigh) +
    canonicalUnlockedPauseCost pre duration target previousPauser
      removedIndex arrayLength lastTarget

/- Exact forward construction of the complete `pause` source on the direct
singleton-removal path.  Exact one-word calldata makes the short-data LT zero,
so the untaken generic revert needs no execution premise. -/
private theorem exact_pause_runCompiledTo
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {pauser expiry duration previousPauser countValue decrementedCount target
      arrayLength decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1019)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + exactPauseCost pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre pause
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let suffixCost := canonicalUnlockedPauseCost pre duration target
    previousPauser removedIndex arrayLength lastTarget
  let branchCost := gVerylow + gHigh
  let boundPushCost := pushCost (Nat.toB256 36).toBytes.sig
  let branchGas := G + suffixCost + branchCost
  let ltGas := branchGas + gVerylow
  let calldataGas := ltGas + gBase
  let suffixPre := pre.setMach ⟨stack, pre.memory, G + suffixCost⟩
  let branchPre := pre.setMach ⟨0 :: stack, pre.memory, branchGas⟩
  let ltPre := pre.setMach
    ⟨Nat.toB256 36 :: Nat.toB256 36 :: stack, pre.memory, ltGas⟩
  let calldataPre := pre.setMach
    ⟨Nat.toB256 36 :: stack, pre.memory, calldataGas⟩
  have hsuffixCostEq : canonicalUnlockedPauseCost suffixPre duration target
      previousPauser removedIndex arrayLength lastTarget = suffixCost := by
    change pushCost (4 : B256).toBytes.sig + gVerylow +
          checkNonAddressPauseCost + (gVerylow + gHigh) +
          (pushCost lockKey.toBytes.sig + gasWarmAccess + gVerylow +
            (gVerylow + gHigh + gJumpdest) +
            (pushCost (1 : B256).toBytes.sig + pushCost lockKey.toBytes.sig +
              gasWarmAccess +
                authorizedLiveExpiryPauseCost suffixPre duration target
                  previousPauser removedIndex arrayLength lastTarget)) =
      pushCost (4 : B256).toBytes.sig + gVerylow +
          checkNonAddressPauseCost + (gVerylow + gHigh) +
          (pushCost lockKey.toBytes.sig + gasWarmAccess + gVerylow +
            (gVerylow + gHigh + gJumpdest) +
            (pushCost (1 : B256).toBytes.sig + pushCost lockKey.toBytes.sig +
              gasWarmAccess +
                authorizedLiveExpiryPauseCost pre duration target
                  previousPauser removedIndex arrayLength lastTarget))
    rw [authorizedLiveExpiryPauseCost_eq_of_memory_accessed
      (left := suffixPre) (right := pre) rfl rfl]
  have hsuffixGas : suffixPre.gasLeft = G +
      canonicalUnlockedPauseCost suffixPre duration target previousPauser
        removedIndex arrayLength lastTarget := by
    simp only [suffixPre, Devm.gasLeft_setMach, hsuffixCostEq]
  rcases canonical_unlocked_pause_runCompiledTo
      (pre := suffixPre) (G := G) (img := img) (stack := stack)
      (pauser := pauser) (expiry := expiry) (duration := duration)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwf hr hmask hlock hdataTarget hcaller hpauserNonzero
      hpauserCanonical hauthorizationStorage hexpiryStorage hlive
      hdurationStorage htargetNonzero htargetCanonical hassignmentStorage
      hpreviousNonzero hpreviousCanonical hcountStorage hcountSub
      harrayLengthBound hindexStorage hlengthStorage hdecrement hlastStorage
      hlastCanonical hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic
      hemptyLookup hpauseLookup hfinishLookup hremoveLookup hafterLookup
      hsetPauserLookup hsuffixGas with
    ⟨raw, suffixRun, rawOutput, suffixPath⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas : branchPre.gasLeft =
      suffixPre.gasLeft + branchCost := by
    simp only [branchPre, suffixPre, Devm.gasLeft_setMach]
    dsimp only [branchGas]
  have hbranchPop : Devm.PopBurnBy [0] branchCost branchPre suffixPre := by
    convert Devm.popBurnBy_setMach (devm := branchPre)
      (x := (0 : B256)) (s := stack) rfl hbranchGas using 1
    all_goals rfl
  let branchRun : Func.RunCompiledTo fs sevm branchPre
      (Func.revert <?> canonicalAddressArg 0
        (pushB256 lockKey ::: tload ::: iszero :::
          ((pushB256 1 ::: pushB256 lockKey ::: tstore :::
            arg 0 +++ tagTop assignmentRegion +++ sload ::: caller ::: eq :::
            ((caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
              ((pushB256 pauseDurationSlot ::: sload :::
                mstoreAt durationWord +++ arg 0 +++ mstoreAt targetWord +++
                pushB256 0 ::: mstoreAt newPauserWord +++
                pushB256 0 ::: mstoreAt previousPauserWord +++
                pushB256 1 ::: mstoreAt continuationWord +++
                .call setPauserSlot) <?>
                  (.call heartbeatExpiredErrorSlot))) <?>
              (.call senderNotPauserErrorSlot))) <?>
            (.call reentrantCallErrorSlot))))
      (.error (.revert, raw)) :=
    .zero hbranchRoom hbranchPop suffixRun
  have branchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) branchRun :=
    .zero (room := hbranchRoom) (pop := hbranchPop)
      (tail := suffixRun) suffixPath
  have hlt : Ninst.RunCompiled sevm ltPre lt branchPre := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by
      simp [B256.ltCheck]) (by
      simp only [ltPre, Devm.gasLeft_setMach]
      dsimp only [ltGas]) (by omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hlt (by simp)
      branchRun branchPath with ⟨ltRun, ltPath⟩
  have hcalldataGas : calldataPre.gasLeft = ltGas + gBase := by
    simp only [calldataPre, Devm.gasLeft_setMach]
    dsimp only [calldataGas]
  have hcalldata : Ninst.RunCompiled sevm calldataPre calldatasize ltPre := by
    simpa only [hdataLength, calldataPre, ltPre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_pushItem (sevm := sevm) (devm := calldataPre)
        (r := .calldatasize) (x := Nat.toB256 sevm.data.length)
        (cost := gBase) (G := ltGas) (by rintro ⟨⟩) rfl hcalldataGas (by
          simp only [calldataPre, Devm.stack_setMach, List.length_cons]
          omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hcalldata (by simp)
      (by simpa only [calldataPre, ltPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using ltRun)
      (by simpa only [calldataPre, ltPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using ltPath) with
    ⟨calldataRun, calldataPath⟩
  have hpushGas : pre.gasLeft = calldataGas + boundPushCost := by
    rw [hgas]
    dsimp only [exactPauseCost, suffixCost, branchCost, boundPushCost,
      branchGas, ltGas, calldataGas]
    omega
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pre) (word := Nat.toB256 36)
      (stack := stack) (c := boundPushCost) (G := calldataGas)
      hstack rfl hpushGas (by omega)
      (by simpa only [calldataPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using calldataRun)
      (by simpa only [calldataPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using calldataPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [pause, requireStaticArgs, prepend] using run,
    rawOutput,
    by simpa only [pause, requireStaticArgs, prepend] using path⟩

/-- The complete exact-pause budget depends on the machine state only through
memory and the warm account set. -/
private theorem exactPauseCost_eq_of_memory_accessed
    {left right : Devm}
    (hmemory : left.memory = right.memory)
    (haccessed : left.accessedAddresses = right.accessedAddresses)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) :
    exactPauseCost left duration target previousPauser removedIndex
        arrayLength lastTarget =
      exactPauseCost right duration target previousPauser removedIndex
        arrayLength lastTarget := by
  dsimp only [exactPauseCost, canonicalUnlockedPauseCost,
    unlockedGuardPauseCost, lockWriteAuthorizedPauseCost]
  rw [authorizedLiveExpiryPauseCost_eq_of_memory_accessed hmemory haccessed]

/-- Exact cost of the first successful comparison in the dispatcher's third
linear group, followed by the complete pause endpoint. -/
private def thirdGroupPauseDispatchCost
    (pre : Devm) (duration target previousPauser removedIndex arrayLength
      lastTarget : B256) : Nat :=
  gVerylow + pushCost (selector "pause" [.address]).toBytes.sig +
    gVerylow + (gVerylow + gHigh + gJumpdest) + gBase +
    exactPauseCost pre duration target previousPauser removedIndex
      arrayLength lastTarget

/- The exact pause selector matches the first entry in the third linear group.
The unmatched remainder and fallback are not executed and need no lookup. -/
private theorem third_group_pause_dispatch_runCompiledTo
    (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {pauser expiry duration previousPauser countValue decrementedCount target
      arrayLength decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = selector "pause" [.address] :: stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1018)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + thirdGroupPauseDispatchCost pre duration
      target previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (linearDispatchWith fallbackSlot ((funcs dp).drop 9 |>.take 4))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let pauseSelector := selector "pause" [.address]
  let pauseCost := exactPauseCost pre duration target previousPauser
    removedIndex arrayLength lastTarget
  let selectorPushCost := pushCost pauseSelector.toBytes.sig
  let branchCost := gVerylow + gHigh + gJumpdest
  let pausePre := pre.setMach ⟨stack, pre.memory, G + pauseCost⟩
  let popPre := pre.setMach
    ⟨pauseSelector :: stack, pre.memory, G + pauseCost + gBase⟩
  let branchPre := pre.setMach
    ⟨1 :: pauseSelector :: stack, pre.memory,
      G + pauseCost + gBase + branchCost⟩
  let eqPre := pre.setMach
    ⟨pauseSelector :: pauseSelector :: pauseSelector :: stack, pre.memory,
      G + pauseCost + gBase + branchCost + gVerylow⟩
  let pushPre := pre.setMach
    ⟨pauseSelector :: pauseSelector :: stack, pre.memory,
      G + pauseCost + gBase + branchCost + gVerylow + selectorPushCost⟩
  have hpauseCostEq : exactPauseCost pausePre duration target previousPauser
      removedIndex arrayLength lastTarget = pauseCost := by
    change exactPauseCost pausePre duration target previousPauser removedIndex
      arrayLength lastTarget = exactPauseCost pre duration target
        previousPauser removedIndex arrayLength lastTarget
    exact exactPauseCost_eq_of_memory_accessed rfl rfl _ _ _ _ _ _
  have hpauseGas : pausePre.gasLeft = G +
      exactPauseCost pausePre duration target previousPauser removedIndex
        arrayLength lastTarget := by
    simp only [pausePre, Devm.gasLeft_setMach, hpauseCostEq]
  rcases exact_pause_runCompiledTo
      (pre := pausePre) (G := G) (img := img) (stack := stack)
      (pauser := pauser) (expiry := expiry) (duration := duration)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwf hr hdataLength hmask hlock hdataTarget hcaller
      hpauserNonzero hpauserCanonical hauthorizationStorage hexpiryStorage
      hlive hdurationStorage htargetNonzero htargetCanonical
      hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage
      hcountSub harrayLengthBound hindexStorage hlengthStorage hdecrement
      hlastStorage hlastCanonical hcodeSize haccess hwarmHole
      hwarmMovedIndex (by omega) hstatic hemptyLookup hpauseLookup
      hfinishLookup hremoveLookup hafterLookup hsetPauserLookup hpauseGas with
    ⟨raw, pauseRun, rawOutput, pausePath⟩
  have hpopGas : popPre.gasLeft = pausePre.gasLeft + gBase := by
    simp only [popPre, pausePre, Devm.gasLeft_setMach]
  have hpop : Ninst.RunCompiled sevm popPre pop pausePre := by
    exact Ninst.runCompiled_pop rfl hpopGas
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hpop (by simp)
      pauseRun pausePath with ⟨popRun, popPath⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas : branchPre.gasLeft =
      popPre.gasLeft + branchCost := by
    simp only [branchPre, popPre, Devm.gasLeft_setMach]
  have hbranchPop : Devm.PopBurnBy [1] branchCost branchPre popPre := by
    convert Devm.popBurnBy_setMach (devm := branchPre)
      (x := (1 : B256)) (s := pauseSelector :: stack) rfl hbranchGas using 1
    all_goals rfl
  let branchRun : Func.RunCompiledTo fs sevm branchPre
      ((pop ::: pause) <?>
        linearDispatchWith fallbackSlot
          [ (selector "MIN_PAUSE_DURATION" [], minPauseDuration dp),
            (selector "MAX_HEARTBEAT_INTERVAL" [],
              maxHeartbeatInterval dp),
            (selector "getPausableCount" [.address], getPausableCount) ])
      (.error (.revert, raw)) :=
    .succ (by decide) hbranchRoom hbranchPop popRun
  have branchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) branchRun :=
    .succ (nonzero := by decide) (room := hbranchRoom)
      (pop := hbranchPop) (tail := popRun) popPath
  have heq : Ninst.RunCompiled sevm eqPre eq branchPre := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by
      simp [B256.eqCheck]) (by
      simp only [eqPre, Devm.gasLeft_setMach]) (by
      simp only [List.length_cons]
      omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) heq (by simp)
      branchRun branchPath with ⟨eqRun, eqPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pushPre) (word := pauseSelector)
      (stack := pauseSelector :: pauseSelector :: stack)
      (c := selectorPushCost)
      (G := G + pauseCost + gBase + branchCost + gVerylow)
      rfl rfl rfl (by simp only [List.length_cons]; omega)
      (by simpa only [pushPre, eqPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using eqRun)
      (by simpa only [pushPre, eqPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using eqPath) with
    ⟨pushRun, pushPath⟩
  have hdupGas : pre.gasLeft =
      (G + pauseCost + gBase + branchCost + gVerylow + selectorPushCost) +
        gVerylow := by
    rw [hgas]
    dsimp only [thirdGroupPauseDispatchCost, pauseSelector, pauseCost,
      selectorPushCost, branchCost]
    omega
  have hdup : Ninst.RunCompiled sevm pre (dup 0) pushPre := by
    simpa only [pushPre, hstack, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_dup (sevm := sevm) (devm := pre) (n := 0)
        (w := pauseSelector)
        (G := G + pauseCost + gBase + branchCost + gVerylow +
          selectorPushCost) (by
          rw [hstack]
          rfl) hdupGas (by
          rw [hstack]
          simp only [List.length_cons]
          omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hdup (by simp)
      (by simpa only [pushPre, pauseSelector, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using pushRun)
      (by simpa only [pushPre, pauseSelector, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using pushPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa [linearDispatchWith, funcs, pauseSelector] using run,
    rawOutput,
    by simpa [linearDispatchWith, funcs, pauseSelector] using path⟩

/-- Exact cost of the two selected hybrid pivots followed by the third-group
pause dispatch. -/
private def hybridPauseDispatchCost
    (dp : DeployParams) (pre : Devm)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) : Nat :=
  gVerylow +
    pushCost (firstSelector ((funcs dp).drop 9 |>.take 4)).toBytes.sig +
    gVerylow + (gVerylow + gHigh) +
    gVerylow +
    pushCost (firstSelector ((funcs dp).drop 13)).toBytes.sig +
    gVerylow + (gVerylow + gHigh + gJumpdest) +
    thirdGroupPauseDispatchCost pre duration target previousPauser
      removedIndex arrayLength lastTarget

/- The outer pause pivot compares equal and takes the right half; the inner
fourth-group pivot is greater than the pause selector and takes the textual
third group.  Neither unselected half is executed. -/
set_option maxRecDepth 2048 in
private theorem hybrid_pause_dispatch_runCompiledTo
    (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {pauser expiry duration previousPauser countValue decrementedCount target
      arrayLength decrementedLength removedIndex lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = selector "pause" [.address] :: stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1017)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + hybridPauseDispatchCost dp pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (hybridDispatchWith fallbackSlot (funcs dp))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let pauseSelector := selector "pause" [.address]
  let outerPivot := firstSelector ((funcs dp).drop 9 |>.take 4)
  let innerPivot := firstSelector ((funcs dp).drop 13)
  let thirdCost := thirdGroupPauseDispatchCost pre duration target
    previousPauser removedIndex arrayLength lastTarget
  let outerPushCost := pushCost outerPivot.toBytes.sig
  let innerPushCost := pushCost innerPivot.toBytes.sig
  let outerBranchCost := gVerylow + gHigh
  let innerBranchCost := gVerylow + gHigh + gJumpdest
  let thirdPre := pre.setMach
    ⟨pauseSelector :: stack, pre.memory, G + thirdCost⟩
  let innerBranchPre := pre.setMach
    ⟨1 :: pauseSelector :: stack, pre.memory,
      G + thirdCost + innerBranchCost⟩
  let innerGtPre := pre.setMach
    ⟨innerPivot :: pauseSelector :: pauseSelector :: stack, pre.memory,
      G + thirdCost + innerBranchCost + gVerylow⟩
  let innerPushPre := pre.setMach
    ⟨pauseSelector :: pauseSelector :: stack, pre.memory,
      G + thirdCost + innerBranchCost + gVerylow + innerPushCost⟩
  let innerPre := pre.setMach
    ⟨pauseSelector :: stack, pre.memory,
      G + thirdCost + innerBranchCost + gVerylow + innerPushCost +
        gVerylow⟩
  let outerBranchPre := pre.setMach
    ⟨0 :: pauseSelector :: stack, pre.memory,
      G + thirdCost + innerBranchCost + gVerylow + innerPushCost +
        gVerylow + outerBranchCost⟩
  let outerGtPre := pre.setMach
    ⟨outerPivot :: pauseSelector :: pauseSelector :: stack, pre.memory,
      G + thirdCost + innerBranchCost + gVerylow + innerPushCost +
        gVerylow + outerBranchCost + gVerylow⟩
  let outerPushPre := pre.setMach
    ⟨pauseSelector :: pauseSelector :: stack, pre.memory,
      G + thirdCost + innerBranchCost + gVerylow + innerPushCost +
        gVerylow + outerBranchCost + gVerylow + outerPushCost⟩
  have hthirdCostEq : thirdGroupPauseDispatchCost thirdPre duration target
      previousPauser removedIndex arrayLength lastTarget = thirdCost := by
    change gVerylow + pushCost (selector "pause" [.address]).toBytes.sig +
          gVerylow + (gVerylow + gHigh + gJumpdest) + gBase +
          exactPauseCost thirdPre duration target previousPauser removedIndex
            arrayLength lastTarget =
      gVerylow + pushCost (selector "pause" [.address]).toBytes.sig +
          gVerylow + (gVerylow + gHigh + gJumpdest) + gBase +
          exactPauseCost pre duration target previousPauser removedIndex
            arrayLength lastTarget
    rw [exactPauseCost_eq_of_memory_accessed
      (left := thirdPre) (right := pre) rfl rfl]
  have hthirdGas : thirdPre.gasLeft = G +
      thirdGroupPauseDispatchCost thirdPre duration target previousPauser
        removedIndex arrayLength lastTarget := by
    simp only [thirdPre, Devm.gasLeft_setMach, hthirdCostEq]
  rcases third_group_pause_dispatch_runCompiledTo dp
      (pre := thirdPre) (G := G) (img := img) (stack := stack)
      (pauser := pauser) (expiry := expiry) (duration := duration)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwf hr hdataLength hmask hlock hdataTarget hcaller
      hpauserNonzero hpauserCanonical hauthorizationStorage hexpiryStorage
      hlive hdurationStorage htargetNonzero htargetCanonical
      hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage
      hcountSub harrayLengthBound hindexStorage hlengthStorage hdecrement
      hlastStorage hlastCanonical hcodeSize haccess hwarmHole
      hwarmMovedIndex (by omega) hstatic hemptyLookup hpauseLookup
      hfinishLookup hremoveLookup hafterLookup hsetPauserLookup hthirdGas with
    ⟨raw, thirdRun, rawOutput, thirdPath⟩
  have hinnerValue : B256.gtCheck innerPivot pauseSelector = 1 := by
    dsimp [innerPivot, pauseSelector, funcs, firstSelector]
    rfl
  have hinnerBranchRoom : innerBranchPre.stack.length < 1024 := by
    simp only [innerBranchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hinnerBranchGas : innerBranchPre.gasLeft =
      thirdPre.gasLeft + innerBranchCost := by
    simp only [innerBranchPre, thirdPre, Devm.gasLeft_setMach]
  have hinnerBranchPop : Devm.PopBurnBy [1] innerBranchCost innerBranchPre
      thirdPre := by
    convert Devm.popBurnBy_setMach (devm := innerBranchPre)
      (x := (1 : B256)) (s := pauseSelector :: stack) rfl
        hinnerBranchGas using 1
    all_goals rfl
  let innerBranchRun : Func.RunCompiledTo fs sevm innerBranchPre
      ((linearDispatchWith fallbackSlot ((funcs dp).drop 9 |>.take 4)) <?>
        linearDispatchWith fallbackSlot ((funcs dp).drop 13))
      (.error (.revert, raw)) :=
    .succ (by decide) hinnerBranchRoom hinnerBranchPop thirdRun
  have innerBranchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) innerBranchRun :=
    .succ (nonzero := by decide) (room := hinnerBranchRoom)
      (pop := hinnerBranchPop) (tail := thirdRun) thirdPath
  have hinnerGt : Ninst.RunCompiled sevm innerGtPre gt innerBranchPre := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl hinnerValue (by
      simp only [innerGtPre, Devm.gasLeft_setMach]) (by
      simp only [List.length_cons]
      omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hinnerGt (by simp)
      innerBranchRun innerBranchPath with ⟨innerGtRun, innerGtPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := innerPushPre) (word := innerPivot)
      (stack := pauseSelector :: pauseSelector :: stack)
      (c := innerPushCost)
      (G := G + thirdCost + innerBranchCost + gVerylow)
      rfl rfl rfl (by simp only [List.length_cons]; omega)
      (by simpa only [innerPushPre, innerGtPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using innerGtRun)
      (by simpa only [innerPushPre, innerGtPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using innerGtPath) with
    ⟨innerPushRun, innerPushPath⟩
  have hinnerDupGas : innerPre.gasLeft = innerPushPre.gasLeft + gVerylow := by
    simp only [innerPre, innerPushPre, Devm.gasLeft_setMach]
  have hinnerDup : Ninst.RunCompiled sevm innerPre (dup 0) innerPushPre := by
    simpa only [innerPre, innerPushPre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_dup (sevm := sevm) (devm := innerPre) (n := 0)
        (w := pauseSelector)
        (G := G + thirdCost + innerBranchCost + gVerylow + innerPushCost)
        (by rfl)
        hinnerDupGas (by
          simp only [innerPre, Devm.stack_setMach, List.length_cons]
          omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hinnerDup (by simp)
      (by simpa only [innerPushPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using innerPushRun)
      (by simpa only [innerPushPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using innerPushPath) with
    ⟨innerRun, innerPath⟩
  have houterPivot : outerPivot = pauseSelector := by
    rfl
  have houterBranchRoom : outerBranchPre.stack.length < 1024 := by
    simp only [outerBranchPre, Devm.stack_setMach, List.length_cons]
    omega
  have houterBranchGas : outerBranchPre.gasLeft =
      innerPre.gasLeft + outerBranchCost := by
    simp only [outerBranchPre, innerPre, Devm.gasLeft_setMach]
  have houterBranchPop : Devm.PopBurnBy [0] outerBranchCost outerBranchPre
      innerPre := by
    convert Devm.popBurnBy_setMach (devm := outerBranchPre)
      (x := (0 : B256)) (s := pauseSelector :: stack) rfl
        houterBranchGas using 1
    all_goals rfl
  let outerBranchRun : Func.RunCompiledTo fs sevm outerBranchPre
      ((splitDispatch (firstSelector ((funcs dp).drop 5 |>.take 4))
          (linearDispatchWith fallbackSlot ((funcs dp).take 5))
          (linearDispatchWith fallbackSlot ((funcs dp).drop 5 |>.take 4)))
        <?>
        splitDispatch innerPivot
          (linearDispatchWith fallbackSlot ((funcs dp).drop 9 |>.take 4))
          (linearDispatchWith fallbackSlot ((funcs dp).drop 13)))
      (.error (.revert, raw)) :=
    .zero houterBranchRoom houterBranchPop (by
      simpa only [splitDispatch, innerPivot] using innerRun)
  have outerBranchPath : Func.RunCompiledTo.DirectPausePath
      sevm.currentTarget target (phase := .beforeWrite) outerBranchRun :=
    .zero (room := houterBranchRoom) (pop := houterBranchPop)
      (tail := by simpa only [splitDispatch, innerPivot] using innerRun)
      (by simpa only [splitDispatch, innerPivot] using innerPath)
  have houterGt : Ninst.RunCompiled sevm outerGtPre gt outerBranchPre := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by
      rw [houterPivot]
      simp [B256.gtCheck]) (by
      simp only [outerGtPre, Devm.gasLeft_setMach]) (by
      simp only [List.length_cons]
      omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) houterGt (by simp)
      outerBranchRun outerBranchPath with ⟨outerGtRun, outerGtPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := outerPushPre) (word := outerPivot)
      (stack := pauseSelector :: pauseSelector :: stack)
      (c := outerPushCost)
      (G := G + thirdCost + innerBranchCost + gVerylow + innerPushCost +
        gVerylow + outerBranchCost + gVerylow)
      rfl rfl rfl (by simp only [List.length_cons]; omega)
      (by simpa only [outerPushPre, outerGtPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
          using outerGtRun)
      (by simpa only [outerPushPre, outerGtPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
          using outerGtPath) with
    ⟨outerPushRun, outerPushPath⟩
  have houterDupGas : pre.gasLeft = outerPushPre.gasLeft + gVerylow := by
    rw [hgas]
    dsimp only [hybridPauseDispatchCost, pauseSelector, outerPivot,
      innerPivot, thirdCost, outerPushCost, innerPushCost, outerBranchCost,
      innerBranchCost, thirdPre, innerBranchPre, innerGtPre, innerPushPre,
      innerPre, outerBranchPre, outerGtPre, outerPushPre]
    simp only [Devm.gasLeft_setMach]
    omega
  have houterDup : Ninst.RunCompiled sevm pre (dup 0) outerPushPre := by
    simpa only [outerPushPre, hstack, pauseSelector, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_dup (sevm := sevm) (devm := pre) (n := 0)
        (w := pauseSelector)
        (G := G + thirdCost + innerBranchCost + gVerylow + innerPushCost +
          gVerylow + outerBranchCost + gVerylow + outerPushCost) (by
          rw [hstack]
          rfl) houterDupGas (by
          rw [hstack]
          simp only [List.length_cons]
          omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) houterDup (by simp)
      (by simpa only [outerPushPre, pauseSelector, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using outerPushRun)
      (by simpa only [outerPushPre, pauseSelector, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using outerPushPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa [hybridDispatchWith, splitDispatch, outerPivot, innerPivot]
      using run,
    rawOutput,
    by simpa [hybridDispatchWith, splitDispatch, outerPivot, innerPivot]
      using path⟩

/-- Exact phase-preserving prepend for the four-instruction selector extractor. -/
private theorem directPausePath_prepend_fsig
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {selectorWord selectedTarget markedTarget : B256}
    {stack : List B256} {G : Nat} {rest : Func} {out : Execution}
    {phase : DirectPausePhase}
    (hstack : pre.stack = stack)
    (hdata : Sevm.dataWord sevm 0 = selectorWord)
    (hshift : selectorWord >>> 224 = selectedTarget)
    (hgas : pre.gasLeft = G + pushCost (0 : B256).toBytes.sig +
      gVerylow + pushCost (224 : B256).toBytes.sig + gVerylow)
    (hroom : stack.length < 1023)
    (tail : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨selectedTarget :: stack, pre.memory, G⟩) rest out)
    (tailPath : Func.RunCompiledTo.DirectPausePath sevm.currentTarget
      markedTarget (phase := phase) tail) :
    ∃ run : Func.RunCompiledTo fs sevm pre (fsig +++ rest) out,
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget markedTarget
        (phase := phase) run := by
  let shrPre := pre.setMach
    ⟨(224 : B256) :: selectorWord :: stack, pre.memory, G + gVerylow⟩
  let shrPushPre := pre.setMach
    ⟨selectorWord :: stack, pre.memory,
      G + gVerylow + pushCost (224 : B256).toBytes.sig⟩
  let loadPre := pre.setMach
    ⟨(0 : B256) :: stack, pre.memory,
      G + gVerylow + pushCost (224 : B256).toBytes.sig + gVerylow⟩
  have hshr : Ninst.RunCompiled sevm shrPre shr
      (pre.setMach ⟨selectedTarget :: stack, pre.memory, G⟩) := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl (by
      exact hshift) (by
      simp only [shrPre, Devm.gasLeft_setMach]) (by omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := markedTarget) hshr (by simp)
      tail tailPath with ⟨shrRun, shrPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := markedTarget)
      (phase := phase) (pre := shrPushPre) (word := 224)
      (stack := selectorWord :: stack)
      (c := pushCost (224 : B256).toBytes.sig) (G := G + gVerylow)
      rfl rfl rfl (by simp only [List.length_cons]; omega)
      (by simpa only [shrPushPre, shrPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using shrRun)
      (by simpa only [shrPushPre, shrPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using shrPath) with
    ⟨shrPushRun, shrPushPath⟩
  have hload : Ninst.RunCompiled sevm loadPre calldataload shrPushPre := by
    simpa only [loadPre, shrPushPre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_calldataload
        (sevm := sevm) (devm := loadPre) (x := 0) (v := selectorWord)
        (s := stack)
        (G := G + gVerylow + pushCost (224 : B256).toBytes.sig)
        rfl hdata (by simp only [loadPre, Devm.gasLeft_setMach])
        (by omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := markedTarget) hload (by simp)
      (by simpa only [shrPushPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using shrPushRun)
      (by simpa only [shrPushPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using shrPushPath) with
    ⟨loadRun, loadPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := markedTarget)
      (phase := phase) (pre := pre) (word := 0) (stack := stack)
      (c := pushCost (0 : B256).toBytes.sig)
      (G := G + gVerylow + pushCost (224 : B256).toBytes.sig + gVerylow)
      hstack rfl hgas (by omega)
      (by simpa only [loadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using loadRun)
      (by simpa only [loadPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using loadPath) with
    ⟨run, path⟩
  norm_num [fsig, cdl, shiftRight, prepend] at *
  exact ⟨run, path⟩

/-- The hybrid pause dispatch budget depends on machine state only through
memory and the warm account set. -/
private theorem hybridPauseDispatchCost_eq_of_memory_accessed
    {left right : Devm}
    (hmemory : left.memory = right.memory)
    (haccessed : left.accessedAddresses = right.accessedAddresses)
    (dp : DeployParams)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) :
    hybridPauseDispatchCost dp left duration target previousPauser
        removedIndex arrayLength lastTarget =
      hybridPauseDispatchCost dp right duration target previousPauser
        removedIndex arrayLength lastTarget := by
  dsimp only [hybridPauseDispatchCost, thirdGroupPauseDispatchCost]
  rw [exactPauseCost_eq_of_memory_accessed hmemory haccessed]

/-- Exact cost of selector extraction followed by the selected hybrid pause
dispatcher path. -/
private def fsigHybridPauseDispatchCost
    (dp : DeployParams) (pre : Devm)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) : Nat :=
  pushCost (0 : B256).toBytes.sig + gVerylow +
    pushCost (224 : B256).toBytes.sig + gVerylow +
    hybridPauseDispatchCost dp pre duration target previousPauser removedIndex
      arrayLength lastTarget

/- Selector extraction produces the pause selector, after which the two
selected hybrid pivots reach the exact pause endpoint. -/
private theorem fsig_hybrid_pause_dispatch_runCompiledTo
    (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {selectorWord pauser expiry duration previousPauser countValue
      decrementedCount target arrayLength decrementedLength removedIndex
      lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hselectorData : Sevm.dataWord sevm 0 = selectorWord)
    (hselectorShift : selectorWord >>> 224 = selector "pause" [.address])
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1017)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + fsigHybridPauseDispatchCost dp pre duration
      target previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre
        (fsig +++ hybridDispatchWith fallbackSlot (funcs dp))
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let hybridCost := hybridPauseDispatchCost dp pre duration target
    previousPauser removedIndex arrayLength lastTarget
  let hybridPre := pre.setMach
    ⟨selector "pause" [.address] :: stack, pre.memory, G + hybridCost⟩
  have hhybridCostEq : hybridPauseDispatchCost dp hybridPre duration target
      previousPauser removedIndex arrayLength lastTarget = hybridCost := by
    exact hybridPauseDispatchCost_eq_of_memory_accessed rfl rfl dp duration
      target previousPauser removedIndex arrayLength lastTarget
  have hhybridGas : hybridPre.gasLeft = G +
      hybridPauseDispatchCost dp hybridPre duration target previousPauser
        removedIndex arrayLength lastTarget := by
    simp only [hybridPre, Devm.gasLeft_setMach, hhybridCostEq]
  rcases hybrid_pause_dispatch_runCompiledTo dp
      (pre := hybridPre) (G := G) (img := img) (stack := stack)
      (pauser := pauser) (expiry := expiry) (duration := duration)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hwf hr hdataLength hmask hlock hdataTarget hcaller
      hpauserNonzero hpauserCanonical hauthorizationStorage hexpiryStorage
      hlive hdurationStorage htargetNonzero htargetCanonical
      hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage
      hcountSub harrayLengthBound hindexStorage hlengthStorage hdecrement
      hlastStorage hlastCanonical hcodeSize haccess hwarmHole
      hwarmMovedIndex hroom hstatic hemptyLookup hpauseLookup hfinishLookup
      hremoveLookup hafterLookup hsetPauserLookup hhybridGas with
    ⟨raw, hybridRun, rawOutput, hybridPath⟩
  have hfsigGas : pre.gasLeft =
      (G + hybridCost) + pushCost (0 : B256).toBytes.sig + gVerylow +
        pushCost (224 : B256).toBytes.sig + gVerylow := by
    rw [hgas]
    dsimp only [fsigHybridPauseDispatchCost, hybridCost]
    omega
  rcases directPausePath_prepend_fsig
      (pre := pre) (selectorWord := selectorWord)
      (selectedTarget := selector "pause" [.address])
      (markedTarget := target) (stack := stack) (G := G + hybridCost)
      (phase := .beforeWrite) hstack hselectorData hselectorShift hfsigGas
      (by omega)
      (by simpa only [hybridPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using hybridRun)
      (by simpa only [hybridPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using hybridPath) with
    ⟨run, path⟩
  exact ⟨raw, run, rawOutput, path⟩

/-- The selector-and-hybrid budget depends on machine state only through
memory and the warm account set. -/
private theorem fsigHybridPauseDispatchCost_eq_of_memory_accessed
    {left right : Devm}
    (hmemory : left.memory = right.memory)
    (haccessed : left.accessedAddresses = right.accessedAddresses)
    (dp : DeployParams)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) :
    fsigHybridPauseDispatchCost dp left duration target previousPauser
        removedIndex arrayLength lastTarget =
      fsigHybridPauseDispatchCost dp right duration target previousPauser
        removedIndex arrayLength lastTarget := by
  dsimp only [fsigHybridPauseDispatchCost]
  rw [hybridPauseDispatchCost_eq_of_memory_accessed hmemory haccessed]

/-- Exact cost of the successful nonpayable/calldata guard followed by selector
extraction and the selected hybrid pause path. -/
private def runtimeMainPauseCost
    (dp : DeployParams) (pre : Devm)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) : Nat :=
  gBase + pushCost (4 : B256).toBytes.sig + gBase + gVerylow + gVerylow +
    (gVerylow + gHigh) +
    fsigHybridPauseDispatchCost dp pre duration target previousPauser
      removedIndex arrayLength lastTarget

/- Exact execution of `runtimeMain` when value is zero and one ABI word is
present.  Both guard values are zero, so the revert arm is not executed. -/
private theorem runtimeMain_pause_runCompiledTo
    (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {selectorWord pauser expiry duration previousPauser countValue
      decrementedCount target arrayLength decrementedLength removedIndex
      lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hvalue : sevm.value = 0)
    (hselectorData : Sevm.dataWord sevm 0 = selectorWord)
    (hselectorShift : selectorWord >>> 224 = selector "pause" [.address])
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1017)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup : fs[emptyRevertSlot]? = some Func.revert)
    (hpauseLookup : fs[pauseAfterSetSlot]? = some pauseAfterSet)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hsetPauserLookup : fs[setPauserSlot]? = some setPauserKernel)
    (hgas : pre.gasLeft = G + runtimeMainPauseCost dp pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw, ∃ run : Func.RunCompiledTo fs sevm pre (runtimeMain dp)
        (.error (.revert, raw)),
      raw.output = [] ∧
      Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
        (phase := .beforeWrite) run := by
  let bodyCost := fsigHybridPauseDispatchCost dp pre duration target
    previousPauser removedIndex arrayLength lastTarget
  let branchCost := gVerylow + gHigh
  let bodyPre := pre.setMach ⟨stack, pre.memory, G + bodyCost⟩
  let branchPre := pre.setMach
    ⟨(0 : B256) :: stack, pre.memory, G + bodyCost + branchCost⟩
  let orPre := pre.setMach
    ⟨(0 : B256) :: (0 : B256) :: stack, pre.memory,
      G + bodyCost + branchCost + gVerylow⟩
  let ltPre := pre.setMach
    ⟨Nat.toB256 36 :: (4 : B256) :: (0 : B256) :: stack, pre.memory,
      G + bodyCost + branchCost + gVerylow + gVerylow⟩
  let calldataPre := pre.setMach
    ⟨(4 : B256) :: (0 : B256) :: stack, pre.memory,
      G + bodyCost + branchCost + gVerylow + gVerylow + gBase⟩
  let pushPre := pre.setMach
    ⟨(0 : B256) :: stack, pre.memory,
      G + bodyCost + branchCost + gVerylow + gVerylow + gBase +
        pushCost (4 : B256).toBytes.sig⟩
  have hbodyCostEq : fsigHybridPauseDispatchCost dp bodyPre duration target
      previousPauser removedIndex arrayLength lastTarget = bodyCost := by
    exact fsigHybridPauseDispatchCost_eq_of_memory_accessed rfl rfl dp
      duration target previousPauser removedIndex arrayLength lastTarget
  have hbodyGas : bodyPre.gasLeft = G +
      fsigHybridPauseDispatchCost dp bodyPre duration target previousPauser
        removedIndex arrayLength lastTarget := by
    simp only [bodyPre, Devm.gasLeft_setMach, hbodyCostEq]
  rcases fsig_hybrid_pause_dispatch_runCompiledTo dp
      (pre := bodyPre) (G := G) (img := img) (stack := stack)
      (selectorWord := selectorWord) (pauser := pauser) (expiry := expiry)
      (duration := duration) (previousPauser := previousPauser)
      (countValue := countValue) (decrementedCount := decrementedCount)
      (target := target) (arrayLength := arrayLength)
      (decrementedLength := decrementedLength) (removedIndex := removedIndex)
      (lastTarget := lastTarget) rfl hselectorData hselectorShift hwf hr
      hdataLength hmask hlock hdataTarget hcaller hpauserNonzero
      hpauserCanonical hauthorizationStorage hexpiryStorage hlive
      hdurationStorage htargetNonzero htargetCanonical hassignmentStorage
      hpreviousNonzero hpreviousCanonical hcountStorage hcountSub
      harrayLengthBound hindexStorage hlengthStorage hdecrement hlastStorage
      hlastCanonical hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic
      hemptyLookup hpauseLookup hfinishLookup hremoveLookup hafterLookup
      hsetPauserLookup hbodyGas with
    ⟨raw, bodyRun, rawOutput, bodyPath⟩
  have hbranchRoom : branchPre.stack.length < 1024 := by
    simp only [branchPre, Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas : branchPre.gasLeft = bodyPre.gasLeft + branchCost := by
    simp only [branchPre, bodyPre, Devm.gasLeft_setMach]
  have hbranchPop : Devm.PopBurnBy [0] branchCost branchPre bodyPre := by
    convert Devm.popBurnBy_setMach (devm := branchPre)
      (x := (0 : B256)) (s := stack) rfl hbranchGas using 1
    all_goals rfl
  let branchRun : Func.RunCompiledTo fs sevm branchPre
      (Func.revert <?> (fsig +++ hybridDispatchWith fallbackSlot (funcs dp)))
      (.error (.revert, raw)) :=
    .zero hbranchRoom hbranchPop bodyRun
  have branchPath : Func.RunCompiledTo.DirectPausePath sevm.currentTarget
      target (phase := .beforeWrite) branchRun :=
    .zero (room := hbranchRoom) (pop := hbranchPop) (tail := bodyRun)
      bodyPath
  have hor : Ninst.RunCompiled sevm orPre Ninst.or branchPre := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl rfl (by
      simp only [orPre, Devm.gasLeft_setMach]) (by omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hor (by simp)
      branchRun branchPath with ⟨orRun, orPath⟩
  have hltValue : B256.ltCheck (Nat.toB256 36) (4 : B256) = 0 := by
    simp [B256.ltCheck]
    intro h
    have hh := B256.toNat_lt_toNat h
    change 36 ↾ 256 < 4 ↾ 256 at hh
    rw [Nat.lo_eq_of_lt (by norm_num : 36 < 2 ^ 256),
      Nat.lo_eq_of_lt (by norm_num : 4 < 2 ^ 256)] at hh
    omega
  have hlt : Ninst.RunCompiled sevm ltPre lt orPre := by
    exact Ninst.runCompiled_binary (by rintro ⟨⟩) rfl rfl hltValue (by
      simp only [ltPre, Devm.gasLeft_setMach]) (by
      simp only [List.length_cons]
      omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hlt (by simp)
      (by simpa only [orPre, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using orRun)
      (by simpa only [orPre, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using orPath) with
    ⟨ltRun, ltPath⟩
  have hcalldata : Ninst.RunCompiled sevm calldataPre calldatasize ltPre := by
    simpa only [hdataLength, calldataPre, ltPre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_pushItem (sevm := sevm) (devm := calldataPre)
        (r := .calldatasize) (x := Nat.toB256 sevm.data.length)
        (cost := gBase)
        (G := G + bodyCost + branchCost + gVerylow + gVerylow)
        (by rintro ⟨⟩) rfl (by
          simp only [calldataPre, Devm.gasLeft_setMach]) (by
          simp only [calldataPre, Devm.stack_setMach, List.length_cons]
          omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hcalldata (by simp)
      (by simpa only [calldataPre, ltPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using ltRun)
      (by simpa only [calldataPre, ltPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using ltPath) with
    ⟨calldataRun, calldataPath⟩
  rcases directPausePath_prepend_pushB256
      (ca := sevm.currentTarget) (target := target)
      (phase := .beforeWrite) (pre := pushPre) (word := 4)
      (stack := (0 : B256) :: stack)
      (c := pushCost (4 : B256).toBytes.sig)
      (G := G + bodyCost + branchCost + gVerylow + gVerylow + gBase)
      rfl rfl rfl (by simp only [List.length_cons]; omega)
      (by simpa only [pushPre, calldataPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using calldataRun)
      (by simpa only [pushPre, calldataPre, Devm.setMach_setMach,
          Devm.stack_setMach, Devm.memory_setMach] using calldataPath) with
    ⟨pushRun, pushPath⟩
  have hcallvalueGas : pre.gasLeft = pushPre.gasLeft + gBase := by
    rw [hgas]
    dsimp only [runtimeMainPauseCost, bodyCost, branchCost, pushPre]
    simp only [Devm.gasLeft_setMach]
    omega
  have hcallvalue : Ninst.RunCompiled sevm pre callvalue pushPre := by
    simpa only [hstack, hvalue, pushPre, Devm.setMach_setMach,
        Devm.stack_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_pushItem (sevm := sevm) (devm := pre)
        (r := .callvalue) (x := sevm.value) (cost := gBase)
        (G := G + bodyCost + branchCost + gVerylow + gVerylow + gBase +
          pushCost (4 : B256).toBytes.sig)
        (by rintro ⟨⟩) rfl hcallvalueGas (by
          rw [hstack]
          omega)
  rcases directPausePath_prepend_childless
      (ca := sevm.currentTarget) (target := target) hcallvalue (by simp)
      (by simpa only [pushPre, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using pushRun)
      (by simpa only [pushPre, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using pushPath) with
    ⟨run, path⟩
  exact ⟨raw,
    by simpa only [runtimeMain] using run,
    rawOutput,
    by simpa only [runtimeMain] using path⟩

/-- The guarded runtime-main budget depends on machine state only through
memory and the warm account set. -/
private theorem runtimeMainPauseCost_eq_of_memory_accessed
    {left right : Devm}
    (hmemory : left.memory = right.memory)
    (haccessed : left.accessedAddresses = right.accessedAddresses)
    (dp : DeployParams)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) :
    runtimeMainPauseCost dp left duration target previousPauser removedIndex
        arrayLength lastTarget =
      runtimeMainPauseCost dp right duration target previousPauser removedIndex
        arrayLength lastTarget := by
  dsimp only [runtimeMainPauseCost]
  rw [fsigHybridPauseDispatchCost_eq_of_memory_accessed hmemory haccessed]

/-- Exact program-entry cost followed by the selected runtime-main pause path. -/
def runtimePauseCost
    (dp : DeployParams) (pre : Devm)
    (duration target previousPauser removedIndex arrayLength lastTarget :
      B256) : Nat :=
  gJumpdest + runtimeMainPauseCost dp pre duration target previousPauser
    removedIndex arrayLength lastTarget

/- Enter the compiled runtime at its leading `JUMPDEST`, retaining the exact
main-function derivation that carries the direct-pause path certificate. -/
private theorem runtime_pause_runCompiledTo
    (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {selectorWord pauser expiry duration previousPauser countValue
      decrementedCount target arrayLength decrementedLength removedIndex
      lastTarget : B256}
    {G : Nat}
    (hstack : pre.stack = stack)
    (hvalue : sevm.value = 0)
    (hselectorData : Sevm.dataWord sevm 0 = selectorWord)
    (hselectorShift : selectorWord >>> 224 = selector "pause" [.address])
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1017)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup :
      ((runtime dp).main :: (runtime dp).aux)[emptyRevertSlot]? =
        some Func.revert)
    (hpauseLookup :
      ((runtime dp).main :: (runtime dp).aux)[pauseAfterSetSlot]? =
        some pauseAfterSet)
    (hfinishLookup :
      ((runtime dp).main :: (runtime dp).aux)[finishSetPauserSlot]? =
        some finishSetPauser)
    (hremoveLookup :
      ((runtime dp).main :: (runtime dp).aux)[removeTargetSlot]? =
        some removeTarget)
    (hafterLookup :
      ((runtime dp).main :: (runtime dp).aux)[afterOldPauserSlot]? =
        some afterOldPauser)
    (hsetPauserLookup :
      ((runtime dp).main :: (runtime dp).aux)[setPauserSlot]? =
        some setPauserKernel)
    (hgas : pre.gasLeft = G + runtimePauseCost dp pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw mid,
      ∃ mainRun : Func.RunCompiledTo
          ((runtime dp).main :: (runtime dp).aux) sevm mid
          (runtime dp).main (.error (.revert, raw)),
        Prog.RunCompiledTo sevm pre (runtime dp) (.error (.revert, raw)) ∧
        Devm.BurnBy gJumpdest pre mid ∧
        mid = pre.setMach ⟨stack, pre.memory,
          G + runtimeMainPauseCost dp pre duration target previousPauser
            removedIndex arrayLength lastTarget⟩ ∧
        raw.output = [] ∧
        Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
          (phase := .beforeWrite) mainRun := by
  let mainCost := runtimeMainPauseCost dp pre duration target previousPauser
    removedIndex arrayLength lastTarget
  let mid := pre.setMach ⟨stack, pre.memory, G + mainCost⟩
  have hmainCostEq : runtimeMainPauseCost dp mid duration target
      previousPauser removedIndex arrayLength lastTarget = mainCost := by
    exact runtimeMainPauseCost_eq_of_memory_accessed rfl rfl dp duration
      target previousPauser removedIndex arrayLength lastTarget
  have hmainGas : mid.gasLeft = G + runtimeMainPauseCost dp mid duration
      target previousPauser removedIndex arrayLength lastTarget := by
    simp only [mid, Devm.gasLeft_setMach, hmainCostEq]
  rcases runtimeMain_pause_runCompiledTo dp
      (fs := (runtime dp).main :: (runtime dp).aux) (pre := mid) (G := G)
      (img := img) (stack := stack) (selectorWord := selectorWord)
      (pauser := pauser) (expiry := expiry) (duration := duration)
      (previousPauser := previousPauser) (countValue := countValue)
      (decrementedCount := decrementedCount) (target := target)
      (arrayLength := arrayLength) (decrementedLength := decrementedLength)
      (removedIndex := removedIndex) (lastTarget := lastTarget)
      rfl hvalue hselectorData hselectorShift hwf hr hdataLength hmask hlock
      hdataTarget hcaller hpauserNonzero hpauserCanonical
      hauthorizationStorage hexpiryStorage hlive hdurationStorage
      htargetNonzero htargetCanonical hassignmentStorage hpreviousNonzero
      hpreviousCanonical hcountStorage hcountSub harrayLengthBound
      hindexStorage hlengthStorage hdecrement hlastStorage hlastCanonical
      hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic hemptyLookup
      hpauseLookup hfinishLookup hremoveLookup hafterLookup hsetPauserLookup
      hmainGas with
    ⟨raw, mainRun, rawOutput, mainPath⟩
  have hentryGas : pre.gasLeft = (G + mainCost) + gJumpdest := by
    rw [hgas]
    dsimp only [runtimePauseCost, mainCost]
    omega
  have programRun : Prog.RunCompiledTo sevm pre (runtime dp)
      (.error (.revert, raw)) := by
    apply Prog.runCompiledTo_intro (G := G + mainCost) (mid := mid)
      hentryGas
    · simp only [mid, hstack]
    · simpa only [runtime] using mainRun
  have entryBurn : Devm.BurnBy gJumpdest pre mid := by
    simpa only [mid, hstack] using Devm.burnBy_setMach_gas hentryGas
  exact ⟨raw, mid,
    by simpa only [runtime] using mainRun,
    programRun, entryBurn, rfl, rawOutput,
    by simpa only [runtime] using mainPath⟩

/-- Construction-only transport from an exact compiled main-function walk to
the corresponding executions at pc 1 and at the program-entry pc 0. -/
private theorem directPausePath_exec_of_program_main
    {p : Prog} {sevm : Sevm} {pre mid raw : Devm} {target : B256}
    (hcode : some sevm.code.toList = p.compile)
    (hentryBurn : Devm.BurnBy gJumpdest pre mid)
    (mainRun : Func.RunCompiledTo (p.main :: p.aux) sevm mid p.main
      (.error (.revert, raw)))
    (mainPath : Func.RunCompiledTo.DirectPausePath sevm.currentTarget target
      (phase := .beforeWrite) mainRun) :
    ∃ _mainExec : Exec 1 sevm mid (.error (.revert, raw)),
      ∃ rootExec : Exec 0 sevm pre (.error (.revert, raw)),
        ∃ _rootPath : Exec.DirectPausePath sevm.currentTarget target
            (phase := .beforeWrite) rootExec,
          ∃ write : Exec.SuccessfulSstoreOccurrence
              (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            write.storageOwner = sevm.currentTarget ∧
            write.key = assignmentSlot target ∧ write.value = 0 := by
  have hcode' : some sevm.code.toList =
      Prog.compile ⟨p.main, p.aux⟩ := hcode
  have hget : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some hcode' hget with ⟨hjumpdest, hsubcode⟩
  have hnopush : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table hcode' hget).2
  rcases Func.RunCompiledTo.exists_exec_directPausePath mainRun mainPath
      hcode' rfl 1 hsubcode hnopush with ⟨mainExec, mainExecPath⟩
  have hentry : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont hjumpdest hentryBurn
  have entryChildless : ∀ operation : Xinst,
      ¬ Ninst.At sevm.code 0 (.exec operation) :=
    fun _ operationAt => operationAt.false_of_jinstAt hjumpdest
  let rootExec : Exec 0 sevm pre (.error (.revert, raw)) :=
    .cont hentry mainExec
  have rootPath : Exec.DirectPausePath sevm.currentTarget target
      (phase := .beforeWrite) rootExec :=
    .cont entryChildless mainExecPath
  rcases rootPath.beforeWriteEvidence.1 with
    ⟨write, owner, key, value, zeroCode, zeroInstruction, zeroStack,
      zeroSize, order⟩
  exact ⟨mainExec, rootExec, rootPath, write, owner, key, value⟩

/- The exact runtime construction yields both the pc-1 main execution and the
pc-0 program execution, while retaining the source-path witness on `mainRun`. -/
private theorem runtime_pause_exec
    (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256}
    {selectorWord pauser expiry duration previousPauser countValue
      decrementedCount target arrayLength decrementedLength removedIndex
      lastTarget : B256}
    {G : Nat}
    (hcode : some sevm.code.toList = (runtime dp).compile)
    (hstack : pre.stack = stack)
    (hvalue : sevm.value = 0)
    (hselectorData : Sevm.dataWord sevm 0 = selectorWord)
    (hselectorShift : selectorWord >>> 224 = selector "pause" [.address])
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1017)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup :
      ((runtime dp).main :: (runtime dp).aux)[emptyRevertSlot]? =
        some Func.revert)
    (hpauseLookup :
      ((runtime dp).main :: (runtime dp).aux)[pauseAfterSetSlot]? =
        some pauseAfterSet)
    (hfinishLookup :
      ((runtime dp).main :: (runtime dp).aux)[finishSetPauserSlot]? =
        some finishSetPauser)
    (hremoveLookup :
      ((runtime dp).main :: (runtime dp).aux)[removeTargetSlot]? =
        some removeTarget)
    (hafterLookup :
      ((runtime dp).main :: (runtime dp).aux)[afterOldPauserSlot]? =
        some afterOldPauser)
    (hsetPauserLookup :
      ((runtime dp).main :: (runtime dp).aux)[setPauserSlot]? =
        some setPauserKernel)
    (hgas : pre.gasLeft = G + runtimePauseCost dp pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw mid,
      ∃ _mainRun : Func.RunCompiledTo
          ((runtime dp).main :: (runtime dp).aux) sevm mid
          (runtime dp).main (.error (.revert, raw)),
        Prog.RunCompiledTo sevm pre (runtime dp) (.error (.revert, raw)) ∧
        Devm.BurnBy gJumpdest pre mid ∧
        mid = pre.setMach ⟨stack, pre.memory,
          G + runtimeMainPauseCost dp pre duration target previousPauser
            removedIndex arrayLength lastTarget⟩ ∧
        raw.output = [] ∧
        ∃ _mainExec : Exec 1 sevm mid (.error (.revert, raw)),
          ∃ rootExec : Exec 0 sevm pre (.error (.revert, raw)),
            ∃ _rootPath : Exec.DirectPausePath sevm.currentTarget target
                (phase := .beforeWrite) rootExec,
              ∃ write : Exec.SuccessfulSstoreOccurrence
                  (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ :
                    Exec.Deriv),
                write.storageOwner = sevm.currentTarget ∧
                write.key = assignmentSlot target ∧ write.value = 0 := by
  rcases runtime_pause_runCompiledTo dp
      (sevm := sevm) (pre := pre) (G := G) (img := img) (stack := stack)
      (selectorWord := selectorWord) (pauser := pauser) (expiry := expiry)
      (duration := duration) (previousPauser := previousPauser)
      (countValue := countValue) (decrementedCount := decrementedCount)
      (target := target) (arrayLength := arrayLength)
      (decrementedLength := decrementedLength) (removedIndex := removedIndex)
      (lastTarget := lastTarget) hstack hvalue hselectorData hselectorShift
      hwf hr hdataLength hmask hlock hdataTarget hcaller hpauserNonzero
      hpauserCanonical hauthorizationStorage hexpiryStorage hlive
      hdurationStorage htargetNonzero htargetCanonical hassignmentStorage
      hpreviousNonzero hpreviousCanonical hcountStorage hcountSub
      harrayLengthBound hindexStorage hlengthStorage hdecrement hlastStorage
      hlastCanonical hcodeSize haccess hwarmHole hwarmMovedIndex hroom hstatic
      hemptyLookup hpauseLookup hfinishLookup hremoveLookup hafterLookup
      hsetPauserLookup hgas with
    ⟨raw, mid, mainRun, programRun, entryBurn, hmid, rawOutput, mainPath⟩
  rcases directPausePath_exec_of_program_main hcode entryBurn mainRun
      mainPath with
    ⟨mainExec, rootExec, rootPath, write, owner, key, value⟩
  exact ⟨raw, mid, mainRun, programRun, entryBurn, hmid, rawOutput,
    mainExec, rootExec, rootPath, write, owner, key, value⟩

/-- An exact direct `pause` message whose post-write code-size check observes
an empty target reaches the constructed raw revert, settles it as an error,
and restores the Registry witness from message entry.  The occurrence claims
range over the complete root execution, including reverted writes and nested
raw nodes; this is a forward construction, not error-path exhaustiveness. -/
theorem pause_direct_postWrite_revert_settles_and_restores_registry
    (dp : DeployParams)
    {msg : Msg} {sevm : Sevm} {pre : Devm}
    {ca : Adr} {entries : List Entry}
    {img : Bytes} {stack : List B256}
    {selectorWord pauser expiry duration previousPauser countValue
      decrementedCount target arrayLength decrementedLength removedIndex
      lastTarget : B256}
    {G : Nat}
    (hmsgTarget : msg.target = some ca)
    (hmsgOwner : msg.currentTarget = ca)
    (hmsgCodeAddress : msg.codeAddress = some ca)
    (hmsgCode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hmsgValue : msg.value = 0)
    (hmsgData : msg.data = pauseCalldata target)
    (howner : sevm.currentTarget = ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hframeEntry :
      (Frame.ofCall msg).enter = .run ⟨0, sevm, pre⟩)
    (hentry : RegistryWitness
      (logicalStorageOfStor (msg.benv.state.getStor ca)) entries)
    (hstack : pre.stack = stack)
    (hvalue : sevm.value = 0)
    (hselectorData : Sevm.dataWord sevm 0 = selectorWord)
    (hselectorShift : selectorWord >>> 224 = selector "pause" [.address])
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1017)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup :
      ((runtime dp).main :: (runtime dp).aux)[emptyRevertSlot]? =
        some Func.revert)
    (hpauseLookup :
      ((runtime dp).main :: (runtime dp).aux)[pauseAfterSetSlot]? =
        some pauseAfterSet)
    (hfinishLookup :
      ((runtime dp).main :: (runtime dp).aux)[finishSetPauserSlot]? =
        some finishSetPauser)
    (hremoveLookup :
      ((runtime dp).main :: (runtime dp).aux)[removeTargetSlot]? =
        some removeTarget)
    (hafterLookup :
      ((runtime dp).main :: (runtime dp).aux)[afterOldPauserSlot]? =
        some afterOldPauser)
    (hsetPauserLookup :
      ((runtime dp).main :: (runtime dp).aux)[setPauserSlot]? =
        some setPauserKernel)
    (hgas : pre.gasLeft = G + runtimePauseCost dp pre duration target
      previousPauser removedIndex arrayLength lastTarget) :
    ∃ raw,
      Prog.RunCompiledTo sevm pre (runtime dp) (.error (.revert, raw)) ∧
      ∃ rootExec : Exec 0 sevm pre (.error (.revert, raw)),
        raw.output = [] ∧
        ((∃ write : Exec.SuccessfulSstoreOccurrence
            (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
          write.storageOwner = ca ∧
          write.key = assignmentSlot target ∧
          write.value = 0 ∧
          ∃ zeroCode : Exec.NinstOccurrence
              (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            zeroCode.instruction = .reg .extcodesize ∧
            (∃ rest, zeroCode.node.devm.stack = target :: rest) ∧
            (zeroCode.node.devm.getCode target.toAdr).size = 0 ∧
            Exec.RawBefore
              (root :=
                ⟨0, sevm, pre, .error (.revert, raw), rootExec⟩)
              write.occurrence.node zeroCode.node) ∧
          ∀ occurrence : Exec.NinstOccurrence
              (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            occurrence.instruction ≠ .exec .call ∧
            occurrence.instruction ≠ .exec .staticcall) ∧
        ∃ post,
          ProcessMessage msg
              (.some ⟨⟨0, sevm, pre⟩, .error (.revert, raw)⟩)
              (.ok post) ∧
          post.error.isSome ∧
          RegistryWitness
            (logicalStorageOfStor (Devm.getStor post ca)) entries := by
  have hcode : some sevm.code.toList = (runtime dp).compile := by
    rw [hbytes, lidoCircuitBreakerCode_compile]
  rcases runtime_pause_exec dp hcode hstack hvalue hselectorData
      hselectorShift hwf hr hdataLength hmask hlock hdataTarget hcaller
      hpauserNonzero hpauserCanonical hauthorizationStorage hexpiryStorage
      hlive hdurationStorage htargetNonzero htargetCanonical
      hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage
      hcountSub harrayLengthBound hindexStorage hlengthStorage hdecrement
      hlastStorage hlastCanonical hcodeSize haccess hwarmHole hwarmMovedIndex
      hroom hstatic hemptyLookup hpauseLookup hfinishLookup hremoveLookup
      hafterLookup hsetPauserLookup hgas with
    ⟨raw, _mid, _mainRun, programRun, _entryBurn, _hmid, rawOutput,
      _mainExec, rootExec, rootPath, _write, _owner, _key, _value⟩
  have evidence := rootPath.beforeWriteEvidence
  let post := (raw.withError (some .revert)).rollback msg.benv.state
    msg.tenv.transientStorage
  have hprocess : ProcessMessage msg
      (.some ⟨⟨0, sevm, pre⟩, .error (.revert, raw)⟩)
      (.ok post) := by
    change RunFrame (Frame.ofCall msg)
      (.some ⟨⟨0, sevm, pre⟩, .error (.revert, raw)⟩)
      (.ok post)
    have hrun := RunFrame.of_run
      (raw := .error (.revert, raw)) hframeEntry
    simpa [post, Frame.ofCall, Frame.settle, Frame.settleMsg,
      executeCode.handleError, processMessage.settle, Devm.error,
      Devm.withError, Devm.setMeta] using hrun
  have herror : post.error.isSome :=
    ProcessMessage.error_isSome_of_raw_revert hprocess
  have hpostWitness := pause_settled_error_restores_registry dp
    hmsgTarget hmsgOwner hmsgCodeAddress hmsgCode hmsgValue hmsgData
    htargetCanonical hentry hprocess herror
  rcases evidence.1 with
    ⟨write, writeOwner, writeKey, writeValue, zeroCode, zeroInstruction,
      zeroStack, zeroSize, order⟩
  refine ⟨raw, programRun, rootExec, rawOutput, ?_, ?_⟩
  · refine ⟨?_, evidence.2⟩
    exact ⟨write, writeOwner.trans howner, writeKey, writeValue, zeroCode,
      zeroInstruction, zeroStack, zeroSize, order⟩
  · exact ⟨post, hprocess, herror, hpostWitness⟩

/-- Memory image after the target-word `MLOAD` on the target-zero path. -/
private def setPauserZeroLoadMemory (pre : Devm) : Mem :=
  (pre.memory.read (targetWord * 32).toNat 32).2

/-- Exact gas consumed from kernel entry through the `PausableZero` terminal. -/
private def setPauserZeroCost (pre : Devm) : Nat :=
  gVerylow +
    (gVerylow + pre.extCost [⟨(targetWord * 32).toNat, 32⟩]) +
    gVerylow +
    (gVerylow + gHigh + gJumpdest) +
    (gVerylow + gMid + gJumpdest) +
    revertSelectorCost
      (pre.setMach ⟨pre.stack, setPauserZeroLoadMemory pre, 0⟩)

/-- The fixed selector emitter contains only childless non-SSTORE `.next`
nodes before its terminal `REVERT`. -/
private theorem runCompiledTo_revertSelector_targetZeroPathFree
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {data : Bytes} {hlen : data.length = 4} {out : Execution}
    (run : Func.RunCompiledTo fs sevm pre (Func.revertSelector data hlen) out) :
    Func.RunCompiledTo.TargetZeroPathFree run := by
  dsimp only [Func.revertSelector] at run
  cases run with
  | next firstRun firstTail =>
      refine .next (instructionRun := firstRun) (tail := firstTail)
        (by simp) (by simp) ?_
      cases firstTail with
      | next secondRun secondTail =>
          refine .next (instructionRun := secondRun) (tail := secondTail)
            (by unfold Ninst.pushB256; simp)
            (by unfold Ninst.pushB256; simp) ?_
          cases secondTail with
          | next thirdRun thirdTail =>
              refine .next (instructionRun := thirdRun) (tail := thirdTail)
                (by simp) (by simp) ?_
              cases thirdTail with
              | next fourthRun fourthTail =>
                  refine .next (instructionRun := fourthRun)
                    (tail := fourthTail)
                    (by unfold Ninst.pushB256; simp)
                    (by unfold Ninst.pushB256; simp) ?_
                  cases fourthTail with
                  | next fifthRun fifthTail =>
                      refine .next (instructionRun := fifthRun)
                        (tail := fifthTail)
                        (by unfold Ninst.pushB256; simp)
                        (by unfold Ninst.pushB256; simp) ?_
                      cases fifthTail with
                      | last terminalRun =>
                          exact .last (terminalRun := terminalRun)

private lemma Ninst.runCompiled_iszero_zero
    {sevm : Sevm} {pre : Devm} {stack : List B256} {G : Nat}
    (hstack : pre.stack = 0 :: stack)
    (hgas : pre.gasLeft = G + gVerylow)
    (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm pre iszero
      (pre.setMach ⟨1 :: stack, pre.memory, G⟩) := by
  exact Ninst.runCompiled_unary (by rintro ⟨⟩) rfl hstack
    rfl hgas hroom

private theorem targetWord_mul_32_ne_zero :
    targetWord * 32 ≠ (0 : B256) := by
  decide

/-- Forward construction of the exact target-zero source path together with
its path certificate. -/
private theorem setPauser_zero_runCompiledTo_source
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {img : Bytes} {stack : List B256} {target : B256} {G : Nat}
    (herrorLookup : fs[pausableZeroErrorSlot]? = some pausableZeroError)
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (htargetZero : target = 0)
    (halign : pre.memory.size % 32 = 0)
    (hgas : pre.gasLeft = G + setPauserZeroCost pre)
    (hroom : pre.stack.length < 1023) :
    let data := customErrorData "PausableZero"
    let post := (pre.setMach ⟨stack,
      (setPauserZeroLoadMemory pre).write 0 data.toB256.toBytes,
      G⟩).withOutput data
    ∃ run : Func.RunCompiledTo fs sevm pre setPauserKernel
        (.error (.revert, post)),
      Func.RunCompiledTo.TargetZeroPathFree run := by
  have htargetReadZero : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = 0 :=
    htargetRead.trans htargetZero
  have hstackRoom : stack.length < 1023 := by
    rw [← hstack]
    exact hroom
  let offset : B256 := targetWord * 32
  let M : Mem := setPauserZeroLoadMemory pre
  let data : Bytes := customErrorData "PausableZero"
  let loadCost : Nat :=
    gVerylow + pre.extCost [⟨offset.toNat, 32⟩]
  let branchCost : Nat := gVerylow + gHigh + gJumpdest
  let callCost : Nat := gVerylow + gMid + gJumpdest
  let selectorCost : Nat :=
    revertSelectorCost (pre.setMach ⟨stack, M, 0⟩)
  have hoffset : offset ≠ 0 := by
    dsimp only [offset]
    exact targetWord_mul_32_ne_zero
  have hpushGas : pre.gasLeft =
      (G + loadCost + gVerylow + branchCost + callCost + selectorCost) +
        gVerylow := by
    rw [hgas]
    dsimp [setPauserZeroCost, loadCost, branchCost, callCost,
      selectorCost, offset, M]
    rw [hstack]
    omega
  have hpush : Ninst.RunCompiled sevm pre (Ninst.pushB256 offset)
      (pre.setMach ⟨offset :: stack, pre.memory,
        G + loadCost + gVerylow + branchCost + callCost + selectorCost⟩) := by
    simpa only [hstack] using Ninst.runCompiled_pushB256
      (sevm := sevm) (devm := pre) (w := offset) (c := gVerylow)
      (G := G + loadCost + gVerylow + branchCost + callCost + selectorCost)
      (pushCost_of_ne_zero hoffset) hpushGas (by omega)
  have hload : Ninst.RunCompiled sevm
      (pre.setMach ⟨offset :: stack, pre.memory,
        G + loadCost + gVerylow + branchCost + callCost + selectorCost⟩)
      mload
      (pre.setMach ⟨0 :: stack, M,
        G + gVerylow + branchCost + callCost + selectorCost⟩) := by
    have hvalue : Bytes.toB256
        (pre.memory.read offset.toNat 32).1 = 0 := by
      rw [Mem.Reads.read hr]
      exact htargetReadZero
    simpa only [Devm.setMach_setMach] using Ninst.runCompiled_mload_of
      (sevm := sevm) (devm := pre.setMach ⟨offset :: stack, pre.memory,
        G + loadCost + gVerylow + branchCost + callCost + selectorCost⟩)
      (i := offset) (v := (0 : B256)) (s := stack)
      (c := loadCost)
      (G := G + gVerylow + branchCost + callCost + selectorCost)
      (M := M) rfl rfl hvalue rfl (by
        simp only [Devm.gasLeft_setMach]
        omega) (by omega)
  have hiszero : Ninst.RunCompiled sevm
      (pre.setMach ⟨0 :: stack, M,
        G + gVerylow + branchCost + callCost + selectorCost⟩)
      iszero
      (pre.setMach ⟨1 :: stack, M,
        G + branchCost + callCost + selectorCost⟩) := by
    exact Ninst.runCompiled_iszero_zero rfl (by
      simp only [Devm.gasLeft_setMach]
      omega) (by omega)
  have hMwf : Mem.Wf M := by
    dsimp only [M, setPauserZeroLoadMemory]
    exact hwf.extend _ _
  have hMreads : Mem.Reads M img := by
    dsimp only [M, setPauserZeroLoadMemory]
    exact Mem.Reads.extend hr _ _
  have hMalign : M.size % 32 = 0 := by
    dsimp only [M, setPauserZeroLoadMemory, Mem.read, Mem.extend]
    simp only [memExtSize]
    split
    · exact halign
    · simp
  have hdataLength : data.length = 4 := by
    dsimp only [data]
    simp [customErrorData, B256.length_toBytes]
  have hbody : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨stack, M, G + selectorCost⟩)
      pausableZeroError
      (.error (.revert,
        (pre.setMach ⟨stack, M.write 0 data.toB256.toBytes,
          G⟩).withOutput data)) := by
    change Func.RunCompiledTo fs sevm
      (pre.setMach ⟨stack, M, G + selectorCost⟩)
      (Func.revertSelector data hdataLength) _
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Func.runCompiledTo_revertSelector
      (fs := fs) (sevm := sevm) (devm :=
        pre.setMach ⟨stack, M, G + selectorCost⟩)
      (data := data) (img := img) (G := G) hdataLength hMwf hMreads
      hMalign (by
        simp only [Devm.gasLeft_setMach]
        dsimp only [selectorCost]
        rfl) (by simpa only [Devm.stack_setMach] using hstackRoom)
  have hbodyFree :=
    runCompiledTo_revertSelector_targetZeroPathFree
      (hlen := hdataLength) hbody
  have hcallRoom :
      (pre.setMach ⟨stack, M,
        G + callCost + selectorCost⟩).stack.length < 1024 := by
    simp only [Devm.stack_setMach]
    omega
  have hcallGas :
      (pre.setMach ⟨stack, M,
        G + callCost + selectorCost⟩).gasLeft =
        (G + selectorCost) + (gVerylow + gMid + gJumpdest) := by
    simp only [Devm.gasLeft_setMach]
    dsimp only [callCost]
    omega
  have hcallBurn : Devm.BurnBy (gVerylow + gMid + gJumpdest)
      (pre.setMach ⟨stack, M, G + callCost + selectorCost⟩)
      (pre.setMach ⟨stack, M, G + selectorCost⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using Devm.burnBy_setMach_gas hcallGas
  let hcall : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨stack, M,
        G + callCost + selectorCost⟩)
      (.call pausableZeroErrorSlot)
      (.error (.revert,
        (pre.setMach ⟨stack, M.write 0 data.toB256.toBytes,
          G⟩).withOutput data)) :=
    Func.RunCompiledTo.call herrorLookup hcallRoom hcallBurn hbody
  have hcallFree : Func.RunCompiledTo.TargetZeroPathFree hcall := by
    exact .call (lookup := herrorLookup) (room := hcallRoom)
      (burn := hcallBurn) (tail := hbody) hbodyFree
  have hbranchNonzero : (1 : B256) ≠ 0 := by decide
  have hbranchRoom :
      (pre.setMach ⟨1 :: stack, M,
        G + branchCost + callCost + selectorCost⟩).stack.length < 1024 := by
    simp only [Devm.stack_setMach, List.length_cons]
    omega
  have hbranchGas :
      (pre.setMach ⟨1 :: stack, M,
        G + branchCost + callCost + selectorCost⟩).gasLeft =
        (G + callCost + selectorCost) +
          (gVerylow + gHigh + gJumpdest) := by
    simp only [Devm.gasLeft_setMach]
    dsimp only [branchCost]
    omega
  have hbranchPop : Devm.PopBurnBy [1]
      (gVerylow + gHigh + gJumpdest)
      (pre.setMach ⟨1 :: stack, M,
        G + branchCost + callCost + selectorCost⟩)
      (pre.setMach ⟨stack, M,
        G + callCost + selectorCost⟩) := by
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using
      Devm.popBurnBy_setMach (devm :=
        pre.setMach ⟨1 :: stack, M,
          G + branchCost + callCost + selectorCost⟩)
        (x := (1 : B256)) (s := stack) rfl hbranchGas
  let hbranch : Func.RunCompiledTo fs sevm
      (pre.setMach ⟨1 :: stack, M,
        G + branchCost + callCost + selectorCost⟩)
      ((.call pausableZeroErrorSlot) <?>
        (targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
          loadWord newPauserWord +++ targetKey +++ sstore :::
          iszero :::
          ((.call appendTargetSlot) <?>
            (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
              previousCountKey +++ sstore ::: .call afterOldPauserSlot))))
      (.error (.revert,
        (pre.setMach ⟨stack, M.write 0 data.toB256.toBytes,
          G⟩).withOutput data)) :=
    Func.RunCompiledTo.succ hbranchNonzero hbranchRoom hbranchPop hcall
  have hbranchFree : Func.RunCompiledTo.TargetZeroPathFree hbranch := by
    exact .succ (nonzero := hbranchNonzero) (room := hbranchRoom)
      (pop := hbranchPop) (tail := hcall) hcallFree
  let hrun : Func.RunCompiledTo fs sevm pre setPauserKernel
      (.error (.revert,
        (pre.setMach ⟨stack, M.write 0 data.toB256.toBytes,
          G⟩).withOutput data)) := by
    change Func.RunCompiledTo fs sevm pre
      (.next (Ninst.pushB256 offset)
        (.next mload (.next iszero _))) _
    exact .next hpush (.next hload (.next hiszero hbranch))
  have hrunFree : Func.RunCompiledTo.TargetZeroPathFree hrun := by
    refine .next (instructionRun := hpush) (tail :=
      .next hload (.next hiszero hbranch)) ?_ ?_ ?_
    · unfold Ninst.pushB256
      simp
    · unfold Ninst.pushB256
      simp
    · refine .next (instructionRun := hload)
        (tail := .next hiszero hbranch) (by simp) (by simp) ?_
      refine .next (instructionRun := hiszero) (tail := hbranch)
        (by simp) (by simp) hbranchFree
  exact ⟨hrun, hrunFree⟩

/-- The shared Registry kernel's exact compiler-table entry exists for every
deployment parameterization. -/
theorem setPauserKernel_tableEntry (dp : DeployParams) :
    ∃ loc, (table 0 ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
      some (loc, setPauserKernel) := by
  have hsnd :
      Prod.snd <$> (table 0
        ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some setPauserKernel := by
    rw [Prog.get?_table]
    simp [runtime, aux, setPauserSlot]
  cases hentry :
      (table 0 ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? with
  | none => simp [hentry] at hsnd
  | some entry =>
      obtain ⟨loc, body⟩ := entry
      simp [hentry] at hsnd
      subst body
      exact ⟨loc, rfl⟩

/-- Every auxiliary call used by the Registry prefix resolves to its exact
source body in the production runtime table. -/
theorem runtime_registry_lookups (dp : DeployParams) :
    let fs := (runtime dp).main :: (runtime dp).aux
    fs[pausableZeroErrorSlot]? = some pausableZeroError ∧
    fs[appendTargetSlot]? = some appendTarget ∧
    fs[afterOldPauserSlot]? = some afterOldPauser ∧
    fs[removeTargetSlot]? = some removeTarget ∧
    fs[finishSetPauserSlot]? = some finishSetPauser := by
  simp [runtime, aux, pausableZeroErrorSlot, appendTargetSlot,
    afterOldPauserSlot, removeTargetSlot, finishSetPauserSlot]

/-- Every continuation and panic call used after the Registry suffix resolves
to its exact source body in the production runtime table. -/
theorem runtime_caller_lookups (dp : DeployParams) :
    let fs := (runtime dp).main :: (runtime dp).aux
    fs[registerAfterSetSlot]? = some registerAfterSet ∧
    fs[pauseAfterSetSlot]? = some pauseAfterSet ∧
    ∃ panicData,
      fs[arithmeticPanicSlot]? = some (Func.revertData panicData) := by
  simp [runtime, aux, registerAfterSetSlot, pauseAfterSetSlot,
    arithmeticPanicSlot]

/-! ### Concrete post-write direct-pause control -/

private theorem byteArray_ofList_toList (bs : Bytes) :
    (ByteArray.mk bs.toArray).toList = bs := by
  rw [ByteArray.toList_eq_toList_data]

private def directPauseControlTarget : B256 := 7
private def directPauseControlPauser : B256 := 9
private def directPauseControlOwner : Adr := Nat.toAdr 100
private def directPauseControlExpiry : B256 := 20

private def directPauseControlRegistryStor : Stor :=
  applyRegistryWrites .empty
    [(assignmentSlot directPauseControlTarget, directPauseControlPauser),
      (arrayEntrySlot 1, directPauseControlTarget),
      (indexSlot directPauseControlTarget, 1),
      (arrayLengthSlot, 1),
      (countSlot directPauseControlPauser, 1)]

private def directPauseControlStor : Stor :=
  directPauseControlRegistryStor.set
    (expirySlot directPauseControlPauser) directPauseControlExpiry

private theorem directPauseControlStor_witness :
    RegistryWitness (logicalStorageOfStor directPauseControlStor)
      [(directPauseControlTarget, directPauseControlPauser)] := by
  have hfresh := RegistryWitness.applyFreshWrites
    (s := Stor.empty) emptyWitness
    (target := directPauseControlTarget)
    (newPauser := directPauseControlPauser)
    (by
      constructor
      · decide
      · unfold canonicalAddress directPauseControlTarget
        change (7 : Nat) < 2 ^ 160
        norm_num)
    (by
      constructor
      · decide
      · unfold canonicalAddress directPauseControlPauser
        change (9 : Nat) < 2 ^ 160
        norm_num)
    (by rfl)
  have hexpiry := hfresh.expiry_set
    (pauser := directPauseControlPauser)
    (value := directPauseControlExpiry) (by
      unfold canonicalAddress directPauseControlPauser
      change (9 : Nat) < 2 ^ 160
      norm_num)
  norm_num [directPauseControlStor, directPauseControlRegistryStor,
    directPauseControlTarget, directPauseControlPauser,
    directPauseControlExpiry, assignmentCount] at hexpiry ⊢
  exact hexpiry

private def directPauseControlCode : ByteArray :=
  ByteArray.mk (lidoCircuitBreakerCode officialParams).toArray

private def directPauseControlState : State :=
  State.set (.empty : State) directPauseControlOwner
    { Acct.nil with
      stor := directPauseControlStor
      code := directPauseControlCode }

private def directPauseControlBaseMsg : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := directPauseControlState
        stat :=
          { (default : BenvStat) with
            origState := directPauseControlState
            time := 10 } }
    tenv := default
    caller := Nat.toAdr 9
    target := some directPauseControlOwner
    currentTarget := directPauseControlOwner
    gas := 0
    value := 0
    data := pauseCalldata directPauseControlTarget
    codeAddress := some directPauseControlOwner
    code := directPauseControlCode
    depth := 0
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .ofList
      [(directPauseControlOwner,
          arrayEntrySlot (1 : B256)),
        (directPauseControlOwner,
          indexSlot directPauseControlTarget)]
    disablePrecompiles := true }

private def directPauseControlGas : Nat :=
  runtimePauseCost officialParams (initDevm directPauseControlBaseMsg)
    0 directPauseControlTarget directPauseControlPauser 1 1
    directPauseControlTarget

private def directPauseControlMsg : Msg :=
  { directPauseControlBaseMsg with gas := directPauseControlGas }

private def directPauseControlSevm : Sevm :=
  initSevm directPauseControlMsg

private def directPauseControlPre : Devm :=
  initDevm directPauseControlMsg

private theorem directPauseControl_entryWitness :
    RegistryWitness
      (logicalStorageOfStor
        (directPauseControlMsg.benv.state.getStor directPauseControlOwner))
      [(directPauseControlTarget, directPauseControlPauser)] := by
  change RegistryWitness
    (logicalStorageOfStor
      ((directPauseControlState.get directPauseControlOwner).stor)) _
  rw [directPauseControlState, State.get_set_self]
  exact directPauseControlStor_witness

private theorem directPauseControl_preWitness :
    RegistryWitness
      (logicalStorageOfStor
        (Devm.getStor directPauseControlPre directPauseControlOwner))
      [(directPauseControlTarget, directPauseControlPauser)] := by
  change RegistryWitness
    (logicalStorageOfStor
      (directPauseControlMsg.benv.state.getStor directPauseControlOwner)) _
  exact directPauseControl_entryWitness

private theorem directPauseControl_getStor :
    Devm.getStor directPauseControlPre directPauseControlOwner =
      directPauseControlStor := by
  change directPauseControlMsg.benv.state.getStor directPauseControlOwner =
    directPauseControlStor
  change (directPauseControlState.get directPauseControlOwner).stor =
    directPauseControlStor
  rw [directPauseControlState, State.get_set_self]

private theorem directPauseControl_targetCanonical :
    canonicalAddress directPauseControlTarget := by
  unfold canonicalAddress directPauseControlTarget
  change (7 : Nat) < 2 ^ 160
  norm_num

private theorem directPauseControl_pauserCanonical :
    canonicalAddress directPauseControlPauser := by
  unfold canonicalAddress directPauseControlPauser
  change (9 : Nat) < 2 ^ 160
  norm_num

private theorem directPauseControl_registryReads :
    directPauseControlPre.getStorVal directPauseControlOwner
        (assignmentSlot directPauseControlTarget) = directPauseControlPauser ∧
    directPauseControlPre.getStorVal directPauseControlOwner
        (indexSlot directPauseControlTarget) = 1 ∧
    directPauseControlPre.getStorVal directPauseControlOwner
        arrayLengthSlot = 1 ∧
    directPauseControlPre.getStorVal directPauseControlOwner
        (arrayEntrySlot 1) = directPauseControlTarget ∧
    directPauseControlPre.getStorVal directPauseControlOwner
        (countSlot directPauseControlPauser) = 1 := by
  have hw := directPauseControl_preWitness
  have hone : Nat.toB256 1 = (1 : B256) := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (Devm.getStor directPauseControlPre
      directPauseControlOwner).get
        (assignmentSlot directPauseControlTarget) =
      directPauseControlPauser
    simpa [logicalStorageOfStor, assignmentAt,
      directPauseControlTarget, directPauseControlPauser] using
      hw.assignments directPauseControlTarget
        directPauseControl_targetCanonical
  · change (Devm.getStor directPauseControlPre
      directPauseControlOwner).get
        (indexSlot directPauseControlTarget) = 1
    simpa [logicalStorageOfStor, oneBasedIndexAt, hone,
      directPauseControlTarget] using
      hw.indices directPauseControlTarget directPauseControl_targetCanonical
  · change (Devm.getStor directPauseControlPre
      directPauseControlOwner).get arrayLengthSlot = 1
    simpa [logicalStorageOfStor, hone] using hw.lengthWord
  · change (Devm.getStor directPauseControlPre
      directPauseControlOwner).get (arrayEntrySlot 1) =
        directPauseControlTarget
    simpa [logicalStorageOfStor, targetAt, hone,
      directPauseControlTarget] using hw.arrayWords 0 (by simp)
  · change (Devm.getStor directPauseControlPre
      directPauseControlOwner).get
        (countSlot directPauseControlPauser) = 1
    simpa [logicalStorageOfStor, assignmentCount, hone,
      directPauseControlPauser] using
      hw.counts directPauseControlPauser directPauseControl_pauserCanonical

private theorem directPauseControl_expiryRead :
    directPauseControlPre.getStorVal directPauseControlOwner
        (expirySlot directPauseControlPauser) = directPauseControlExpiry := by
  change (Devm.getStor directPauseControlPre directPauseControlOwner).get
      (expirySlot directPauseControlPauser) = directPauseControlExpiry
  rw [directPauseControl_getStor, directPauseControlStor,
    Stor.get_set_self]

private theorem directPauseControl_durationRead :
    directPauseControlPre.getStorVal directPauseControlOwner
        pauseDurationSlot = 0 := by
  change (Devm.getStor directPauseControlPre directPauseControlOwner).get
      pauseDurationSlot = 0
  rw [directPauseControl_getStor, directPauseControlStor,
    Stor.get_set_ne]
  · have hne : ∀ (region : Nat) (payload : B256),
        region < 16 → payload.toNat < 2 ^ 252 →
        region ≠ configRegion →
        slot region payload ≠ pauseDurationSlot := by
      intro region payload hregion hpayload hregionNe
      simpa [pauseDurationSlot] using
        slot_ne_of_region_ne
          (leftRegion := region) (rightRegion := configRegion)
          (left := payload) (right := (0 : B256))
          hregion (by norm_num [configRegion]) hpayload
          (by
            change (0 : Nat) < 2 ^ 252
            norm_num)
          hregionNe
    have htargetPayload : directPauseControlTarget.toNat < 2 ^ 252 := by
      unfold directPauseControlTarget
      change (7 : Nat) < 2 ^ 252
      norm_num
    have hpauserPayload : directPauseControlPauser.toNat < 2 ^ 252 := by
      unfold directPauseControlPauser
      change (9 : Nat) < 2 ^ 252
      norm_num
    have honePayload : (1 : B256).toNat < 2 ^ 252 := by
      change (1 : Nat) < 2 ^ 252
      norm_num
    have hzeroPayload : (0 : B256).toNat < 2 ^ 252 := by
      change (0 : Nat) < 2 ^ 252
      norm_num
    have hassignment : assignmentSlot directPauseControlTarget ≠
        pauseDurationSlot := by
      exact hne assignmentRegion directPauseControlTarget
        (by norm_num [assignmentRegion]) htargetPayload
        (by norm_num [assignmentRegion, configRegion])
    have hentry : arrayEntrySlot 1 ≠ pauseDurationSlot := by
      exact hne arrayRegion 1 (by norm_num [arrayRegion]) honePayload
        (by norm_num [arrayRegion, configRegion])
    have hindex : indexSlot directPauseControlTarget ≠
        pauseDurationSlot := by
      exact hne indexRegion directPauseControlTarget
        (by norm_num [indexRegion]) htargetPayload
        (by norm_num [indexRegion, configRegion])
    have hlength : arrayLengthSlot ≠ pauseDurationSlot := by
      exact hne arrayRegion 0 (by norm_num [arrayRegion]) hzeroPayload
        (by norm_num [arrayRegion, configRegion])
    have hcount : countSlot directPauseControlPauser ≠
        pauseDurationSlot := by
      exact hne countRegion directPauseControlPauser
        (by norm_num [countRegion]) hpauserPayload
        (by norm_num [countRegion, configRegion])
    rw [directPauseControlRegistryStor, applyRegistryWrites_get]
    simp [hassignment, hentry, hindex, hlength, hcount,
      Stor.get, Stor.empty]
  · simpa [expirySlot, pauseDurationSlot] using
      slot_ne_of_region_ne
        (leftRegion := expiryRegion) (rightRegion := configRegion)
        (left := directPauseControlPauser) (right := (0 : B256))
        (by norm_num [expiryRegion]) (by norm_num [configRegion])
        (by
          unfold directPauseControlPauser
          change (9 : Nat) < 2 ^ 252
          norm_num)
        (by
          change (0 : Nat) < 2 ^ 252
          norm_num)
        (by norm_num [expiryRegion, configRegion])

private theorem directPauseControl_frameEntry :
    (Frame.ofCall directPauseControlMsg).enter =
      .run ⟨0, directPauseControlSevm, directPauseControlPre⟩ := by
  rfl

private theorem directPauseControl_codeBytes :
    directPauseControlSevm.code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [directPauseControlSevm, directPauseControlMsg,
    directPauseControlBaseMsg, initSevm, directPauseControlCode] using
    byteArray_ofList_toList (lidoCircuitBreakerCode officialParams)

set_option maxRecDepth 2048 in
private theorem directPauseControl_dataFacts :
    directPauseControlSevm.data.length = 36 ∧
    Sevm.dataWord directPauseControlSevm 4 = directPauseControlTarget ∧
    Sevm.dataWord directPauseControlSevm 0 >>> 224 =
      selector "pause" [.address] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [directPauseControlSevm, directPauseControlMsg,
      directPauseControlBaseMsg, initSevm, pauseCalldata,
      abiSelectorBytes_length, B256.length_toBytes]
  · apply dataWord_of_append
      (e := directPauseControlSevm) (idx := (4 : B256))
      (pre := abiSelectorBytes (selector "pause" [.address]))
      (post := []) (w := directPauseControlTarget)
    · rw [abiSelectorBytes_length]
      rfl
    · rfl
  · decide

set_option maxRecDepth 4096 in
private theorem directPauseControl_gas :
    directPauseControlPre.gasLeft =
      runtimePauseCost officialParams directPauseControlPre 0
        directPauseControlTarget directPauseControlPauser 1 1
        directPauseControlTarget := by
  change directPauseControlGas =
    runtimePauseCost officialParams directPauseControlPre 0
      directPauseControlTarget directPauseControlPauser 1 1
      directPauseControlTarget
  unfold directPauseControlGas
  dsimp only [runtimePauseCost]
  rw [runtimeMainPauseCost_eq_of_memory_accessed
    (left := initDevm directPauseControlBaseMsg)
    (right := directPauseControlPre) rfl rfl officialParams 0
    directPauseControlTarget directPauseControlPauser 1 1
    directPauseControlTarget]

private theorem directPauseControl_machineFacts :
    directPauseControlPre.stack = [] ∧
    Mem.Wf directPauseControlPre.memory ∧
    Mem.Reads directPauseControlPre.memory [] ∧
    directPauseControlPre.getTransVal
      directPauseControlSevm.currentTarget lockKey = 0 ∧
    directPauseControlSevm.caller.toB256 = directPauseControlPauser ∧
    directPauseControlSevm.isStatic = false ∧
    directPauseControlPre.stack.length < 1017 ∧
    (directPauseControlTarget.toAdr ∉
      directPauseControlPre.accessedAddresses) ∧
    (⟨directPauseControlSevm.currentTarget,
        arrayEntrySlot (1 : B256)⟩ : Adr × B256) ∈
      directPauseControlPre.accessedStorageKeys ∧
    (⟨directPauseControlSevm.currentTarget,
        indexSlot directPauseControlTarget⟩ : Adr × B256) ∈
      directPauseControlPre.accessedStorageKeys := by
  refine ⟨rfl, Mem.wf_empty, Mem.reads_empty, ?_, ?_, rfl, ?_,
    ?_, ?_, ?_⟩
  · rfl
  · decide
  · change [].length < 1017
    norm_num
  · change directPauseControlTarget.toAdr ∉
      (Std.HashSet.emptyWithCapacity : AdrSet)
    exact Std.HashSet.not_mem_emptyWithCapacity
  · change (directPauseControlOwner, arrayEntrySlot (1 : B256)) ∈
      Std.HashSet.ofList
        [(directPauseControlOwner, arrayEntrySlot (1 : B256)),
          (directPauseControlOwner, indexSlot directPauseControlTarget)]
    rw [Std.HashSet.mem_ofList]
    simp
  · change (directPauseControlOwner, indexSlot directPauseControlTarget) ∈
      Std.HashSet.ofList
        [(directPauseControlOwner, arrayEntrySlot (1 : B256)),
          (directPauseControlOwner, indexSlot directPauseControlTarget)]
    rw [Std.HashSet.mem_ofList]
    simp

private theorem directPauseControl_zeroCode :
    (directPauseControlPre.getCode directPauseControlTarget.toAdr).size =
      0 := by
  change ((directPauseControlState.get
    directPauseControlTarget.toAdr).code).size = 0
  rw [directPauseControlState, State.get_set_ne]
  · rfl
  · decide

private theorem directPauseControl_run :
    ∃ raw,
      Prog.RunCompiledTo directPauseControlSevm directPauseControlPre
          (runtime officialParams) (.error (.revert, raw)) ∧
      ∃ rootExec : Exec 0 directPauseControlSevm directPauseControlPre
          (.error (.revert, raw)),
        raw.output = [] ∧
        ((∃ write : Exec.SuccessfulSstoreOccurrence
            (⟨0, directPauseControlSevm, directPauseControlPre,
              .error (.revert, raw), rootExec⟩ : Exec.Deriv),
          write.storageOwner = directPauseControlOwner ∧
          write.key = assignmentSlot directPauseControlTarget ∧
          write.value = 0 ∧
          ∃ zeroCode : Exec.NinstOccurrence
              (⟨0, directPauseControlSevm, directPauseControlPre,
                .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            zeroCode.instruction = .reg .extcodesize ∧
            (∃ rest, zeroCode.node.devm.stack =
              directPauseControlTarget :: rest) ∧
            (zeroCode.node.devm.getCode
              directPauseControlTarget.toAdr).size = 0 ∧
            Exec.RawBefore
              (root :=
                ⟨0, directPauseControlSevm, directPauseControlPre,
                  .error (.revert, raw), rootExec⟩)
              write.occurrence.node zeroCode.node) ∧
          ∀ occurrence : Exec.NinstOccurrence
              (⟨0, directPauseControlSevm, directPauseControlPre,
                .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            occurrence.instruction ≠ .exec .call ∧
            occurrence.instruction ≠ .exec .staticcall) ∧
        ∃ post,
          ProcessMessage directPauseControlMsg
              (.some ⟨⟨0, directPauseControlSevm,
                directPauseControlPre⟩, .error (.revert, raw)⟩)
              (.ok post) ∧
          post.error.isSome ∧
          RegistryWitness
            (logicalStorageOfStor
              (Devm.getStor post directPauseControlOwner))
            [(directPauseControlTarget, directPauseControlPauser)] := by
  rcases directPauseControl_dataFacts with
    ⟨hdataLength, hdataTarget, hselectorShift⟩
  rcases directPauseControl_machineFacts with
    ⟨hstack, hwf, hr, hlock, hcaller, hstatic, hroom, haccess,
      hwarmHole, hwarmMovedIndex⟩
  rcases directPauseControl_registryReads with
    ⟨hauthorization, hindex, hlength, hlast, hcount⟩
  rcases runtime_registry_lookups officialParams with
    ⟨_hzero, _happend, hafter, hremove, hfinish⟩
  rcases runtime_caller_lookups officialParams with
    ⟨_hregister, hpause, _hpanic⟩
  have hempty :
      ((runtime officialParams).main ::
        (runtime officialParams).aux)[emptyRevertSlot]? =
          some Func.revert := by
    simp [runtime, aux, emptyRevertSlot]
  have hsetPauser :
      ((runtime officialParams).main ::
        (runtime officialParams).aux)[setPauserSlot]? =
          some setPauserKernel := by
    simp [runtime, aux, setPauserSlot]
  have hmsgCode : directPauseControlMsg.code.toList =
      lidoCircuitBreakerCode officialParams := by
    simpa only [directPauseControlSevm, initSevm] using
      directPauseControl_codeBytes
  exact pause_direct_postWrite_revert_settles_and_restores_registry
    officialParams
    (msg := directPauseControlMsg) (sevm := directPauseControlSevm)
    (pre := directPauseControlPre) (ca := directPauseControlOwner)
    (entries := [(directPauseControlTarget, directPauseControlPauser)])
    (img := []) (stack := [])
    (selectorWord := Sevm.dataWord directPauseControlSevm 0)
    (pauser := directPauseControlPauser)
    (expiry := directPauseControlExpiry) (duration := 0)
    (previousPauser := directPauseControlPauser) (countValue := 1)
    (decrementedCount := 0) (target := directPauseControlTarget)
    (arrayLength := 1) (decrementedLength := 0)
    (removedIndex := 1) (lastTarget := directPauseControlTarget)
    (G := 0)
    (by rfl) (by rfl) (by rfl) hmsgCode (by rfl) (by rfl)
    (by rfl) directPauseControl_codeBytes directPauseControl_frameEntry
    directPauseControl_entryWitness hstack (by rfl) (by rfl)
    hselectorShift hwf hr hdataLength (by decide) hlock hdataTarget
    hcaller (by decide) directPauseControl_pauserCanonical hauthorization
    directPauseControl_expiryRead (by decide) directPauseControl_durationRead
    (by decide) directPauseControl_targetCanonical hauthorization (by decide)
    directPauseControl_pauserCanonical hcount (by decide)
    (by
      change (1 : Nat) < 2 ^ 252
      norm_num)
    hindex hlength (by decide) hlast directPauseControl_targetCanonical
    directPauseControl_zeroCode (Or.inr haccess) hwarmHole
    hwarmMovedIndex hroom hstatic hempty hpause hfinish hremove hafter
    hsetPauser (by simpa using directPauseControl_gas)

/-- A fully inhabited production-runtime control for direct `pause`: target
`7` is assigned to the live caller `9` in a singleton Registry owned by
address `100`, while the target account has empty code.  The actual root
execution performs the assignment-zero write strictly before observing zero
code, performs no `CALL` or `STATICCALL`, then settles the exact raw revert as
an error and restores the entry Registry witness. -/
theorem directPause_zeroCode_postWrite_error_control :
    ∃ (msg : Msg) (sevm : Sevm) (pre : Devm) (raw : Devm),
      msg.target = some (Nat.toAdr 100) ∧
      msg.currentTarget = Nat.toAdr 100 ∧
      msg.codeAddress = some (Nat.toAdr 100) ∧
      msg.code.toList = lidoCircuitBreakerCode officialParams ∧
      msg.value = 0 ∧
      msg.data = pauseCalldata (7 : B256) ∧
      sevm = initSevm msg ∧
      pre = initDevm msg ∧
      (Frame.ofCall msg).enter = .run ⟨0, sevm, pre⟩ ∧
      RegistryWitness
        (logicalStorageOfStor (msg.benv.state.getStor (Nat.toAdr 100)))
        [((7 : B256), (9 : B256))] ∧
      sevm.caller.toB256 = (9 : B256) ∧
      pre.getStorVal (Nat.toAdr 100) (assignmentSlot (7 : B256)) = 9 ∧
      pre.getStorVal (Nat.toAdr 100) (expirySlot (9 : B256)) = 20 ∧
      sevm.benvStat.time < (20 : B256) ∧
      (7 : B256) ≠ 0 ∧
      canonicalAddress (7 : B256) ∧
      (pre.getCode (7 : B256).toAdr).size = 0 ∧
      Prog.RunCompiledTo sevm pre (runtime officialParams)
        (.error (.revert, raw)) ∧
      ∃ rootExec : Exec 0 sevm pre (.error (.revert, raw)),
        raw.output = [] ∧
        ((∃ write : Exec.SuccessfulSstoreOccurrence
            (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
          write.storageOwner = Nat.toAdr 100 ∧
          write.key = assignmentSlot (7 : B256) ∧
          write.value = 0 ∧
          ∃ zeroCode : Exec.NinstOccurrence
              (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            zeroCode.instruction = .reg .extcodesize ∧
            (∃ rest, zeroCode.node.devm.stack = (7 : B256) :: rest) ∧
            (zeroCode.node.devm.getCode (7 : B256).toAdr).size = 0 ∧
            Exec.RawBefore
              (root :=
                ⟨0, sevm, pre, .error (.revert, raw), rootExec⟩)
              write.occurrence.node zeroCode.node) ∧
          ∀ occurrence : Exec.NinstOccurrence
              (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            occurrence.instruction ≠ .exec .call ∧
            occurrence.instruction ≠ .exec .staticcall) ∧
        ∃ post,
          ProcessMessage msg
              (.some ⟨⟨0, sevm, pre⟩, .error (.revert, raw)⟩)
              (.ok post) ∧
          post.error.isSome ∧
          RegistryWitness
            (logicalStorageOfStor (Devm.getStor post (Nat.toAdr 100)))
            [((7 : B256), (9 : B256))] := by
  rcases directPauseControl_run with
    ⟨raw, programRun, rootExec, rawOutput, evidence,
      post, process, postError, restored⟩
  rcases directPauseControl_machineFacts with
    ⟨_hstack, _hwf, _hr, _hlock, hcaller, _hstatic, _hroom,
      _haccess, _hwarmHole, _hwarmMovedIndex⟩
  rcases directPauseControl_registryReads with
    ⟨hassignment, _hindex, _hlength, _hlast, _hcount⟩
  have hmsgCode : directPauseControlMsg.code.toList =
      lidoCircuitBreakerCode officialParams := by
    simpa only [directPauseControlSevm, initSevm] using
      directPauseControl_codeBytes
  refine ⟨directPauseControlMsg, directPauseControlSevm,
    directPauseControlPre, raw, ?_, ?_, ?_, hmsgCode, ?_, ?_, rfl, rfl,
    directPauseControl_frameEntry, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    programRun, rootExec, rawOutput, evidence, post, process, postError,
    restored⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa only [directPauseControlTarget, directPauseControlPauser,
      directPauseControlOwner] using directPauseControl_entryWitness
  · simpa only [directPauseControlPauser] using hcaller
  · simpa only [directPauseControlTarget, directPauseControlPauser,
      directPauseControlOwner] using hassignment
  · simpa only [directPauseControlPauser, directPauseControlOwner,
      directPauseControlExpiry] using directPauseControl_expiryRead
  · decide
  · decide
  · simpa only [directPauseControlTarget] using
      directPauseControl_targetCanonical
  · simpa only [directPauseControlTarget] using
      directPauseControl_zeroCode

set_option maxRecDepth 4096 in
/-- Every canonical target-zero kernel entry satisfying the explicit emitted
code, stack, memory, and exact-gas premises reaches the exact `PausableZero`
revert before any raw `SSTORE` occurrence.  This is a forward construction,
not an exhaustive characterization of kernel errors. -/
theorem setPauser_zero_runCompiledTo_pausableZero_noRegistryWrite
    (dp : DeployParams) {ca : Adr} {sevm : Sevm} {pre : Devm}
    {loc : Nat} {img : Bytes} {stack : List B256}
    {target : B256} {G : Nat}
    (_howner : sevm.currentTarget = ca)
    (_hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (_htargetCanonical : canonicalAddress target)
    (htargetZero : target = 0)
    (halign : pre.memory.size % 32 = 0)
    (hgas : pre.gasLeft = G +
      (gVerylow +
        (gVerylow + pre.extCost [⟨(targetWord * 32).toNat, 32⟩]) +
        gVerylow + (gVerylow + gHigh + gJumpdest) +
        (gVerylow + gMid + gJumpdest) +
        revertSelectorCost (pre.setMach ⟨pre.stack,
          (pre.memory.read (targetWord * 32).toNat 32).2, 0⟩)))
    (hroom : pre.stack.length < 1023) :
    let fs := (runtime dp).main :: (runtime dp).aux
    let data := customErrorData "PausableZero"
    let post := (pre.setMach ⟨stack,
      (pre.memory.read (targetWord * 32).toNat 32).2.write 0
        data.toB256.toBytes, G⟩).withOutput data
    Func.RunCompiledTo fs sevm pre setPauserKernel
        (.error (.revert, post)) ∧
      ∃ execution : Exec (loc + 1) sevm pre (.error (.revert, post)),
        ∀ occurrence : Exec.NinstOccurrence
            (⟨loc + 1, sevm, pre, .error (.revert, post), execution⟩ :
              Exec.Deriv),
          occurrence.instruction ≠ .reg .sstore := by
  dsimp only
  have hgasPrivate : pre.gasLeft = G + setPauserZeroCost pre := by
    simpa only [setPauserZeroCost, setPauserZeroLoadMemory] using hgas
  rcases runtime_registry_lookups dp with
    ⟨herror, _happend, _hafter, _hremove, _hfinish⟩
  rcases setPauser_zero_runCompiledTo_source herror hstack hwf hr
      htargetRead htargetZero halign hgasPrivate hroom with
    ⟨run, runFree⟩
  have hcompiled :
      some sevm.code.toList = Prog.compile (runtime dp) := by
    rw [hbytes, lidoCircuitBreakerCode_compile]
  have hsub := (subcode_of_get?_eq_some hcompiled htable).2
  have hnoPush := (Prog.jumpable_of_get?_table hcompiled htable).2
  rcases Func.RunCompiledTo.exists_exec_targetZeroRawSstoreFree
      run runFree hcompiled rfl (loc + 1) hsub hnoPush with
    ⟨execution, executionFree⟩
  refine ⟨run, execution, ?_⟩
  intro occurrence instructionEq
  apply executionFree.noSstoreAt occurrence.node occurrence.reached
  simpa [instructionEq] using occurrence.decoded

set_option maxRecDepth 2048 in
/-- Invert an actual successful execution at the exact emitted kernel slice
to the source `Func.Run`.  This is the success-only direction; error paths use
forward `RunCompiledTo` constructions instead. -/
theorem setPauserKernel_run_of_exec
    (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat}
    (_howner : sevm.currentTarget = ca)
    (_hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    Func.Run ((runtime dp).main :: (runtime dp).aux)
      sevm pre setPauserKernel final := by
  let pk : Exec.Deriv := ⟨loc + 1, sevm, pre, .ok final, hexec⟩
  have hcompiled :
      some sevm.code.toList = Prog.compile (runtime dp) := by
    rw [hbytes, lidoCircuitBreakerCode_compile]
  have hsub := (subcode_of_get?_eq_some hcompiled htable).2
  exact correct_core (runtime dp).main (runtime dp).aux
    pk setPauserKernel hcompiled hsub

/-- Every successful execution at the exact production kernel slice exposes
the source trace's post-Registry boundary before the continuation suffix. -/
private theorem setPauserKernel_exec_extracts_sourceTrace_of_trace
    (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target newPauser : B256}
    {continuation : B256} {trace : SetPauserSourceTrace}
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
    (hexec : Exec (loc + 1) sevm pre (.ok final))
    (htrace : setPauserSourceTrace entries target newPauser = some trace) :
    ∃ postRegistry postImg,
      Mem.Wf postRegistry.memory ∧
      Mem.Reads postRegistry.memory postImg ∧
      Bytes.toB256
        (postImg.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Bytes.toB256
        (postImg.sliceD (newPauserWord * 32).toNat 32 0) = newPauser ∧
      Bytes.toB256
        (postImg.sliceD (previousPauserWord * 32).toNat 32 0) =
          assignmentAt entries target ∧
      Bytes.toB256
        (postImg.sliceD (continuationWord * 32).toNat 32 0) =
          continuation ∧
      Devm.getStor postRegistry ca =
        applyRegistryWrites (Devm.getStor pre ca) trace.writes ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor postRegistry ca))
        trace.postEntries ∧
      Func.Run ((runtime dp).main :: (runtime dp).aux)
        sevm postRegistry finishSetPauser final := by
  have hrun := setPauserKernel_run_of_exec dp howner hcodeAddress
    hbytes htable hexec
  rcases runtime_registry_lookups dp with
    ⟨herror, happend, hafter, hremove, hfinish⟩
  obtain ⟨postRegistry, postImg, hwfPost, hrPost, htargetPost, hnewPost,
      hpreviousPost, hcontinuationPost, hstorPost, hwPost, -, hfinishRun⟩ :=
    setPauser_run_extracts_sourceTrace hwf hr htargetRead hnewRead
      hcontinuationRead howner hw htarget hnew herror happend hafter hremove
      hfinish hrun htrace
  exact ⟨postRegistry, postImg, hwfPost, hrPost, htargetPost, hnewPost,
    hpreviousPost, hcontinuationPost, hstorPost, hwPost, hfinishRun⟩

/-- Every successful execution at the exact production kernel slice chooses
the model/source trace forced by the nonzero-target guard and exposes its
post-Registry boundary before the continuation suffix. -/
theorem setPauserKernel_exec_extracts_sourceTrace
    (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target newPauser : B256}
    {continuation : B256}
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
    ∃ trace postRegistry postImg,
      setPauserSourceTrace entries target newPauser = some trace ∧
      Mem.Wf postRegistry.memory ∧
      Mem.Reads postRegistry.memory postImg ∧
      Bytes.toB256
        (postImg.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Bytes.toB256
        (postImg.sliceD (newPauserWord * 32).toNat 32 0) = newPauser ∧
      Bytes.toB256
        (postImg.sliceD (previousPauserWord * 32).toNat 32 0) =
          assignmentAt entries target ∧
      Bytes.toB256
        (postImg.sliceD (continuationWord * 32).toNat 32 0) =
          continuation ∧
      Devm.getStor postRegistry ca =
        applyRegistryWrites (Devm.getStor pre ca) trace.writes ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor postRegistry ca))
        trace.postEntries ∧
      Func.Run ((runtime dp).main :: (runtime dp).aux)
        sevm postRegistry finishSetPauser final := by
  have hrun := setPauserKernel_run_of_exec dp howner hcodeAddress
    hbytes htable hexec
  rcases runtime_registry_lookups dp with
    ⟨herror, _happend, _hafter, _hremove, _hfinish⟩
  have htarget0 : target ≠ 0 :=
    (setPauser_run_extracts_nonzero_guard
      hwf hr htargetRead herror hrun).1
  obtain ⟨trace, htrace⟩ :
      ∃ trace, setPauserSourceTrace entries target newPauser = some trace := by
    cases hfind : findEntry entries target <;>
      by_cases hnew0 : newPauser = 0 <;>
      simp [setPauserSourceTrace, setPauser, htarget0, hfind, hnew0]
  rcases setPauserKernel_exec_extracts_sourceTrace_of_trace dp howner
      hcodeAddress hbytes htable hwf hr htargetRead hnewRead
      hcontinuationRead hw htarget hnew hexec htrace with
    ⟨postRegistry, postImg, hwfPost, hrPost, htargetPost, hnewPost,
      hpreviousPost, hcontinuationPost, hstorPost, hwPost, hfinish⟩
  exact ⟨trace, postRegistry, postImg, htrace, hwfPost, hrPost,
    htargetPost, hnewPost, hpreviousPost, hcontinuationPost, hstorPost,
    hwPost, hfinish⟩

/-- A successful exact kernel execution entered from `registerPauser` reaches
the zero continuation and preserves the Registry witness through the complete
`registerAfterSet` continuation. -/
theorem registerPauser_kernel_exec_preserves_registry
    (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target newPauser : B256}
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
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htarget : canonicalAddress target)
    (hnew : canonicalAddress newPauser)
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    ∃ trace,
      setPauserSourceTrace entries target newPauser = some trace ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor final ca)) trace.postEntries := by
  rcases setPauserKernel_exec_extracts_sourceTrace dp howner hcodeAddress
      hbytes htable hwf hr htargetRead hnewRead hcontinuationRead
      hw htarget hnew hexec with
    ⟨trace, postRegistry, postImg, htrace, hwfPost, hrPost, htargetPost, hnewPost,
      hpreviousPost, hcontinuationPost, hstorPost, hwPost, hfinish⟩
  refine ⟨trace, htrace, ?_⟩
  rcases runtime_caller_lookups dp with
    ⟨hregisterLookup, hpauseLookup, panicData, hpanicLookup⟩
  rcases finishSetPauser_run_split_continuation hwfPost hrPost
      hnewPost hpreviousPost htargetPost hcontinuationPost howner
      hregisterLookup hpauseLookup hfinish with
    hregister | hpause
  · rcases hregister with
      ⟨_, registerPre, _hstack, hwfRegister, hrRegister,
        hstorRegister, -, hregisterRun⟩
    have hwRegister : RegistryWitness
        (logicalStorageOfStor (Devm.getStor registerPre ca))
          trace.postEntries := by
      rw [← howner, hstorRegister]
      exact hwPost
    exact registerAfterSet_preserves_registry hwfRegister hrRegister
      hpreviousPost hnewPost howner
      (hw.assignmentAt_canonical target) hnew hwRegister
      hpanicLookup hregisterRun
  · exact (hpause.1 rfl).elim

/-- A successful exact kernel execution entered with a zero new pauser and a
nonzero continuation reaches the `pauseAfterSet` pre-yield boundary.  The
Registry removal is already stable there; no claim is made about the terminal
state after the continuation's external control transfer. -/
theorem pause_kernel_exec_reaches_pauseAfterSet
    (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target continuation : B256}
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
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (hcontinuation : continuation ≠ 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htarget : canonicalAddress target)
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    ∃ trace pausePre pauseImg,
      setPauserSourceTrace entries target 0 = some trace ∧
      Mem.Wf pausePre.memory ∧
      Mem.Reads pausePre.memory pauseImg ∧
      Bytes.toB256
        (pauseImg.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Devm.getStor pausePre ca =
        applyRegistryWrites (Devm.getStor pre ca) trace.writes ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor pausePre ca))
        trace.postEntries ∧
      setPauser entries target 0 = some trace.postEntries ∧
      target ∉ trace.postEntries.map Prod.fst ∧
      (Devm.getStor pausePre ca).get (assignmentSlot target) = 0 ∧
      (Devm.getStor pausePre ca).get (indexSlot target) = 0 ∧
      Func.Run ((runtime dp).main :: (runtime dp).aux)
        sevm pausePre pauseAfterSet final := by
  have hzeroCanonical : canonicalAddress (0 : B256) := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  rcases setPauserKernel_exec_extracts_sourceTrace dp howner hcodeAddress
      hbytes htable hwf hr htargetRead hnewRead hcontinuationRead
      hw htarget hzeroCanonical hexec with
    ⟨trace, postRegistry, postImg, htrace, hwfPost, hrPost, htargetPost, hnewPost,
      hpreviousPost, hcontinuationPost, hstorPost, hwPost, hfinish⟩
  rcases runtime_caller_lookups dp with
    ⟨hregisterLookup, hpauseLookup, _panicData, _hpanicLookup⟩
  rcases finishSetPauser_run_split_continuation hwfPost hrPost
      hnewPost hpreviousPost htargetPost hcontinuationPost howner
      hregisterLookup hpauseLookup hfinish with
    hregister | hpause
  · exact (hcontinuation hregister.1).elim
  · rcases hpause with
      ⟨_, pausePre, _hstack, hwfPause, hrPause, hstorPause,
        -, hpauseRun⟩
    have htarget0 : target ≠ 0 := by
      intro heq
      rw [heq, setPauserSourceTrace_target_zero] at htrace
      contradiction
    have hmodel :=
      (setPauser_sourceTrace_refines_model htarget0 htrace).1
    rcases setPauser_zero_removes hw.targetsNodup htarget0 hmodel with
      ⟨htargetAbsent, hassignment, hindex⟩
    have hstorPause' : Devm.getStor pausePre ca =
        Devm.getStor postRegistry ca := by
      rw [howner] at hstorPause
      exact hstorPause
    have hwPause : RegistryWitness
        (logicalStorageOfStor (Devm.getStor pausePre ca))
          trace.postEntries := by
      rw [hstorPause']
      exact hwPost
    refine ⟨trace, pausePre, postImg, htrace, hwfPause, hrPause, htargetPost,
      hstorPause'.trans hstorPost, hwPause, hmodel, htargetAbsent, ?_, ?_,
      hpauseRun⟩
    · calc
        (Devm.getStor pausePre ca).get (assignmentSlot target) =
            assignmentAt trace.postEntries target := by
          simpa [logicalStorageOfStor] using
            hwPause.assignments target htarget
        _ = 0 := hassignment
    · calc
        (Devm.getStor pausePre ca).get (indexSlot target) =
            Nat.toB256 (oneBasedIndexAt trace.postEntries target) := by
          simpa [logicalStorageOfStor] using hwPause.indices target htarget
        _ = 0 := by rw [hindex]; rfl

/-- A concrete Registry witness makes assignment and index membership
equivalent and pins every found target to its unique array position. -/
theorem membershipEquivalence_registerPauser
    {post : Devm} {ca : Adr} {entries : List Entry}
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries)
    {target : B256} (htarget : canonicalAddress target) :
    ((Devm.getStor post ca).get (assignmentSlot target) ≠ 0 ↔
      target ∈ entries.map Prod.fst) ∧
    ((Devm.getStor post ca).get (indexSlot target) ≠ 0 ↔
      target ∈ entries.map Prod.fst) ∧
    ∀ index pauser, findEntry entries target = some (index, pauser) →
      (Devm.getStor post ca).get (assignmentSlot target) = pauser ∧
      (Devm.getStor post ca).get (indexSlot target) =
        Nat.toB256 (index + 1) ∧
      targetAt entries index = target ∧
      ∀ otherIndex, otherIndex < entries.length →
        targetAt entries otherIndex = target → otherIndex = index := by
  have hassignment :
      (Devm.getStor post ca).get (assignmentSlot target) =
        assignmentAt entries target := by
    simpa [logicalStorageOfStor] using hw.assignments target htarget
  have hindex :
      (Devm.getStor post ca).get (indexSlot target) =
        Nat.toB256 (oneBasedIndexAt entries target) := by
    simpa [logicalStorageOfStor] using hw.indices target htarget
  cases hfind : findEntry entries target with
  | none =>
      have hnotmem := findEntry_none_target_not_mem_targets hfind
      have hassignmentZero := findEntry_none_assignmentAt hfind
      have hindexZero := findEntry_none_oneBasedIndexAt hfind
      refine ⟨?_, ?_, ?_⟩
      · constructor
        · intro hne
          exfalso
          apply hne
          rw [hassignment, hassignmentZero]
        · intro hmem
          exact (hnotmem hmem).elim
      · constructor
        · intro hne
          exfalso
          apply hne
          rw [hindex, hindexZero]
          rfl
        · intro hmem
          exact (hnotmem hmem).elim
      · intro index pauser hsome
        contradiction
  | some found =>
      obtain ⟨foundIndex, foundPauser⟩ := found
      have hentry : (target, foundPauser) ∈ entries :=
        mem_of_findEntry hfind
      have hmem : target ∈ entries.map Prod.fst :=
        List.mem_map.mpr ⟨(target, foundPauser), hentry, rfl⟩
      have hpauserNe : foundPauser ≠ 0 :=
        (hw.pausersValid (target, foundPauser) hentry).1
      have hassignmentFound := findEntry_assignmentAt hfind
      have hindexFound := findEntry_oneBasedIndexAt hfind
      have hassignmentNe :
          (Devm.getStor post ca).get (assignmentSlot target) ≠ 0 := by
        rw [hassignment, hassignmentFound]
        exact hpauserNe
      have hindexBound : foundIndex + 1 < 2 ^ 256 := by
        have hfoundLt := findEntry_index_lt hfind
        have hlengthLt := hw.entries_length_lt_2pow256
        omega
      have hindexNe :
          (Devm.getStor post ca).get (indexSlot target) ≠ 0 := by
        rw [hindex, hindexFound]
        intro hzero
        have hnat := congrArg B256.toNat hzero
        rw [B256.toNat_toB256_of_lt hindexBound,
          B256.toNat_zero] at hnat
        omega
      refine ⟨⟨fun _ => hmem, fun _ => hassignmentNe⟩,
        ⟨fun _ => hmem, fun _ => hindexNe⟩, ?_⟩
      intro index pauser hlookup
      obtain ⟨rfl, rfl⟩ := hlookup
      refine ⟨?_, ?_, findEntry_targetAt hfind, ?_⟩
      · exact hassignment.trans hassignmentFound
      · exact hindex.trans (congrArg Nat.toB256 hindexFound)
      · intro otherIndex hother htargetAt
        have hotherIndex :=
          oneBasedIndexAt_targetAt_of_lt entries hw.targetsNodup hother
        rw [htargetAt] at hotherIndex
        omega

/-- Setting a nonzero canonical target's pauser to zero clears both lookup
slots and the dead array tail, and repairs the moved target's index unless the
removed target was itself the tail. -/
theorem cleanStateAfterRemoval_registerPauser
    {s : Stor} {entries : List Entry} {target : B256}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    {trace : SetPauserSourceTrace}
    (htrace : setPauserSourceTrace entries target 0 = some trace) :
    let post := applyRegistryWrites s trace.writes
    (post.get (assignmentSlot target) = 0 ∧
     post.get (indexSlot target) = 0 ∧
     target ∉ trace.postEntries.map Prod.fst) ∧
    (match findEntry entries target with
     | none =>
         post.get
           (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0
     | some (index, _oldPauser) =>
         post.get (arrayEntrySlot (Nat.toB256 entries.length)) = 0 ∧
         let moved := sourceLastTarget entries
         (moved = target ∨
           post.get (indexSlot moved) = Nat.toB256 (index + 1))) := by
  dsimp only
  have hrefines :=
    setPauser_sourceTrace_refines_model htarget.1 htrace
  have hpostWitness :=
    hw.applySetPauserSourceTrace htarget.2 (by
      unfold canonicalAddress
      change (0 : Nat) < 2 ^ 160
      norm_num) htrace
  have hremoved :=
    setPauser_zero_removes hw.targetsNodup htarget.1 hrefines.1
  have hassignment :
      (applyRegistryWrites s trace.writes).get
          (assignmentSlot target) = 0 := by
    have hread := hpostWitness.assignments target htarget.2
    simpa [logicalStorageOfStor, hremoved.2.1] using hread
  have hindex :
      (applyRegistryWrites s trace.writes).get
          (indexSlot target) = 0 := by
    have hread := hpostWitness.indices target htarget.2
    calc
      _ = Nat.toB256 (oneBasedIndexAt trace.postEntries target) := by
        simpa [logicalStorageOfStor] using hread
      _ = 0 := by rw [hremoved.2.2]; rfl
  refine ⟨⟨hassignment, hindex, hremoved.1⟩, ?_⟩
  cases hfind : findEntry entries target with
  | none =>
      have hwrites :
          trace.writes =
            [(assignmentSlot target, 0),
              (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
              (indexSlot target, Nat.toB256 (entries.length + 1)),
              (arrayLengthSlot, Nat.toB256 (entries.length + 1)),
              (arrayEntrySlot (Nat.toB256 (entries.length + 1)), target),
              (indexSlot target, Nat.toB256 (entries.length + 1)),
              (arrayEntrySlot (Nat.toB256 (entries.length + 1)), 0),
              (arrayLengthSlot, Nat.toB256 entries.length),
              (indexSlot target, 0)] := by
        have hexact :=
          setPauserSourceWrites_absent_zero entries target htarget.1 hfind
        rw [hexact] at hrefines
        exact Option.some.inj hrefines.2.symm
      rw [hwrites]
      have hnext256 := hw.fresh_length_lt_2pow256
      have hnext252 :
          (Nat.toB256 (entries.length + 1)).toNat < 2 ^ 252 := by
        rw [B256.toNat_toB256_of_lt hnext256]
        exact hw.fresh_length_lt_2pow252
      have hnext0 : Nat.toB256 (entries.length + 1) ≠ 0 := by
        intro hzero
        have hnat := congrArg B256.toNat hzero
        rw [B256.toNat_toB256_of_lt hnext256] at hnat
        simp only [B256.toNat_zero] at hnat
        omega
      have hlengthArray :=
        arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt hnext0 hnext252
      have hfamilies :=
        registryAddressFamilies_ne_arrayEntrySlot
          htarget.2 htarget.2 hnext252
      simp only [applyRegistryWrites, List.foldl_cons, List.foldl_nil]
      rw [Stor.get_set_ne _ hfamilies.2.1,
        Stor.get_set_ne _ hlengthArray, Stor.get_set_self]
  | some found =>
      obtain ⟨index, oldPauser⟩ := found
      have hwrites :
          trace.writes =
            [(assignmentSlot target, 0),
              (countSlot oldPauser,
                Nat.toB256 (assignmentCount entries oldPauser - 1)),
              (arrayEntrySlot (Nat.toB256 (index + 1)),
                sourceLastTarget entries),
              (indexSlot (sourceLastTarget entries),
                Nat.toB256 (index + 1)),
              (arrayEntrySlot (Nat.toB256 entries.length), 0),
              (arrayLengthSlot, Nat.toB256 (entries.length - 1)),
              (indexSlot target, 0)] := by
        have hexact :=
          setPauserSourceWrites_found_zero entries target index oldPauser
            htarget.1 hfind
        rw [hexact] at hrefines
        exact Option.some.inj hrefines.2.symm
      constructor
      · rw [hwrites]
        have hlength256 := hw.entries_length_lt_2pow256
        have hlength252 :
            (Nat.toB256 entries.length).toNat < 2 ^ 252 := by
          rw [B256.toNat_toB256_of_lt hlength256]
          exact hw.entries_length_lt_2pow252
        have hlength0 : Nat.toB256 entries.length ≠ 0 := by
          intro hzero
          have hnat := congrArg B256.toNat hzero
          rw [B256.toNat_toB256_of_lt hlength256] at hnat
          simp only [B256.toNat_zero] at hnat
          have hfoundLt := findEntry_index_lt hfind
          omega
        have hlengthArray :=
          arrayLengthSlot_ne_arrayEntrySlot_of_pos_lt
            hlength0 hlength252
        have hfamilies :=
          registryAddressFamilies_ne_arrayEntrySlot
            htarget.2 htarget.2 hlength252
        simp only [applyRegistryWrites, List.foldl_cons, List.foldl_nil]
        rw [Stor.get_set_ne _ hfamilies.2.1,
          Stor.get_set_ne _ hlengthArray, Stor.get_set_self]
      · by_cases hmoved : sourceLastTarget entries = target
        · exact Or.inl hmoved
        · right
          obtain ⟨last, hlast⟩ := last_some_of_findEntry hfind
          have hlastMem := last_mem_of_last entries hlast
          have hlastValid := hw.targetsValid last hlastMem
          have hmovedCanonical :
              canonicalAddress (sourceLastTarget entries) := by
            simpa [sourceLastTarget, hlast] using hlastValid.2
          have hindexBeforeLast : index + 1 < entries.length := by
            have hindexLt := findEntry_index_lt hfind
            by_contra hnot
            have heq : index = entries.length - 1 := by omega
            apply hmoved
            rw [sourceLastTarget, hlast]
            have htargetAt := findEntry_targetAt hfind
            have hlastAt := targetAt_last_of_last entries hlast
            rw [heq, hlastAt] at htargetAt
            exact htargetAt
          have hmodelIndex :=
            oneBasedIndexAt_swapPop_moved_of_lt_last entries hfind
              hw.targetsNodup hlast hindexBeforeLast
          have hmodelIndex' :
              oneBasedIndexAt (swapPop entries index)
                  (sourceLastTarget entries) = index + 1 := by
            simpa [sourceLastTarget, hlast] using hmodelIndex
          have hpostEntries :
              trace.postEntries = swapPop entries index := by
            simpa [setPauser, htarget.1, hfind] using hrefines.1.symm
          have hread :=
            hpostWitness.indices (sourceLastTarget entries) hmovedCanonical
          calc
            _ = Nat.toB256
                (oneBasedIndexAt (swapPop entries index)
                  (sourceLastTarget entries)) := by
              simpa [logicalStorageOfStor, hpostEntries] using hread
            _ = Nat.toB256 (index + 1) :=
              congrArg Nat.toB256 hmodelIndex'

private theorem assignmentCount_eq_count_map
    (entries : List Entry) (pauser : B256) :
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

/-- Registry counts agree with the witness multiplicities, the zero-pauser
count is clear, and the sum of live per-pauser counts is the array length. -/
theorem globalCountConservation_registerPauser
    {post : Devm} {ca : Adr} {entries : List Entry}
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries) :
    (∀ pauser, canonicalAddress pauser →
      (Devm.getStor post ca).get (countSlot pauser) =
        Nat.toB256 (assignmentCount entries pauser)) ∧
    (Devm.getStor post ca).get (countSlot 0) = 0 ∧
    (∑ pauser ∈ (entries.map Prod.snd).toFinset,
      ((Devm.getStor post ca).get (countSlot pauser)).toNat) =
        entries.length := by
  refine ⟨?_, ?_, ?_⟩
  · intro pauser hpauser
    simpa [logicalStorageOfStor] using hw.counts pauser hpauser
  · simpa [logicalStorageOfStor] using hw.zeroCount
  · calc
      (∑ pauser ∈ (entries.map Prod.snd).toFinset,
        ((Devm.getStor post ca).get (countSlot pauser)).toNat) =
          ∑ pauser ∈ (entries.map Prod.snd).toFinset,
            assignmentCount entries pauser := by
              apply Finset.sum_congr rfl
              intro pauser hpauser
              have hpauserMem : pauser ∈ entries.map Prod.snd := by
                simpa using hpauser
              obtain ⟨entry, hentry, hpauserEq⟩ :=
                List.mem_map.mp hpauserMem
              have hcanonical : canonicalAddress pauser := by
                rw [← hpauserEq]
                exact (hw.pausersValid entry hentry).2
              have hcount :
                  (Devm.getStor post ca).get (countSlot pauser) =
                    Nat.toB256 (assignmentCount entries pauser) := by
                simpa [logicalStorageOfStor] using
                  hw.counts pauser hcanonical
              rw [hcount, B256.toNat_toB256_of_lt
                (hw.assignmentCount_lt_2pow256 pauser)]
      _ = ∑ pauser ∈ (entries.map Prod.snd).toFinset,
            (entries.map Prod.snd).count pauser := by
              apply Finset.sum_congr rfl
              intro pauser _
              exact assignmentCount_eq_count_map entries pauser
      _ = entries.length := by
              rw [List.sum_toFinset_count_eq_length]
              simp

end Blanc.LidoCircuitBreaker
