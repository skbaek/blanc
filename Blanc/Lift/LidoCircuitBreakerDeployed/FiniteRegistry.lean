import Blanc.Lift.LidoCircuitBreakerDeployed.RegistryLayout
import Blanc.SlotFootprint

/-!
# Finite observations of the deployed Lido registry

The caller supplies an explicit list of address probes. The whole finite
array is observed, while assignment/index/count equations are promised only
for those probes. No conclusion concerns an address outside that list.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc.LidoCircuitBreaker

/-- The exact finite logical keys queried by a registry observation. -/
def registryQueries (probes : List B256) (length : Nat) : List B256 :=
  arrayLengthSlot ::
    ((List.range length).map fun i => arrayEntrySlot (Nat.toB256 (i + 1))) ++
    probes.flatMap (fun p => [assignmentSlot p, indexSlot p, countSlot p])

/-- Registry agreement on an explicit finite address list, including every
live array cell. Entry-list validity is pure finite data. -/
structure RegistryOn (storage : LogicalStorage) (entries : List Entry)
    (probes : List B256) : Prop where
  lengthLt : entries.length < 2 ^ 252
  targetsNodup : (entries.map Prod.fst).Nodup
  targetsValid : ∀ e ∈ entries, nonzeroCanonicalAddress e.1
  pausersValid : ∀ e ∈ entries, nonzeroCanonicalAddress e.2
  probesValid : ∀ p ∈ probes, canonicalAddress p
  lengthWord : storage.read arrayLengthSlot = Nat.toB256 entries.length
  arrayWords : ∀ i ∈ List.range entries.length,
    storage.read (arrayEntrySlot (Nat.toB256 (i + 1))) = targetAt entries i
  assignments : ∀ p ∈ probes, storage.read (assignmentSlot p) = assignmentAt entries p
  indices : ∀ p ∈ probes, storage.read (indexSlot p) = Nat.toB256 (oneBasedIndexAt entries p)
  counts : ∀ p ∈ probes, storage.read (countSlot p) = Nat.toB256 (assignmentCount entries p)

/-- Executable finite-state check; no enumeration of the address type. -/
def checkRegistryOn (storage : LogicalStorage) (entries : List Entry)
    (probes : List B256) : Bool :=
  decide (entries.length < 2 ^ 252) &&
  decide ((entries.map Prod.fst).Nodup) &&
  entries.all (fun e => decide (e.1 ≠ 0 ∧ e.1.toNat < 2 ^ 160) &&
    decide (e.2 ≠ 0 ∧ e.2.toNat < 2 ^ 160)) &&
  probes.all (fun p => decide (p.toNat < 2 ^ 160)) &&
  decide (storage.read arrayLengthSlot = Nat.toB256 entries.length) &&
  (List.range entries.length).all (fun i =>
    decide (storage.read (arrayEntrySlot (Nat.toB256 (i + 1))) = targetAt entries i)) &&
  probes.all (fun p =>
    decide (storage.read (assignmentSlot p) = assignmentAt entries p) &&
    decide (storage.read (indexSlot p) = Nat.toB256 (oneBasedIndexAt entries p)) &&
    decide (storage.read (countSlot p) = Nat.toB256 (assignmentCount entries p)))

/-- The state checker is equivalent to the promised finite observation. -/
theorem checkRegistryOn_eq_true {storage : LogicalStorage} {entries : List Entry}
    {probes : List B256} :
    checkRegistryOn storage entries probes = true ↔ RegistryOn storage entries probes := by
  constructor
  · intro h
    simp only [checkRegistryOn, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq, and_assoc] at h
    obtain ⟨hlen, hn, he, hp, hl, ha, hm⟩ := h
    exact ⟨hlen, hn, fun e h => ⟨(he e h).1, (he e h).2.1⟩, fun e h => (he e h).2.2,
      hp, hl, ha, fun p h => (hm p h).1, fun p h => (hm p h).2.1,
      fun p h => (hm p h).2.2⟩
  · intro h
    simp only [checkRegistryOn, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq, and_assoc]
    exact ⟨h.lengthLt, h.targetsNodup, fun e he => ⟨(h.targetsValid e he).1, (h.targetsValid e he).2, h.pausersValid e he⟩,
      h.probesValid, h.lengthWord, h.arrayWords,
      fun p hp => ⟨h.assignments p hp, h.indices p hp, h.counts p hp⟩⟩

/-- Live entries are all checked when this finite closure check succeeds. -/
def checkLiveCovered (entries : List Entry) (probes : List B256) : Bool :=
  entries.all fun e => decide (e.1 ∈ probes ∧ e.2 ∈ probes)

theorem checkLiveCovered_eq_true {entries : List Entry} {probes : List B256} :
    checkLiveCovered entries probes = true ↔ ∀ e ∈ entries, e.1 ∈ probes ∧ e.2 ∈ probes := by
  simp only [checkLiveCovered, List.all_eq_true, decide_eq_true_eq]

theorem mem_registryQueries_length (probes : List B256) (length : Nat) :
    arrayLengthSlot ∈ registryQueries probes length := by
  simp only [registryQueries, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, List.mem_flatMap, List.not_mem_nil, or_false, true_or]

theorem mem_registryQueries_array {probes : List B256} {length i : Nat}
    (hi : i ∈ List.range length) :
    arrayEntrySlot (Nat.toB256 (i + 1)) ∈ registryQueries probes length := by
  simp only [registryQueries, List.mem_cons, List.mem_append, or_assoc]
  exact Or.inr (Or.inl (List.mem_map.mpr ⟨i, hi, rfl⟩))

theorem mem_registryQueries_mapping {probes : List B256} {length : Nat} {p key : B256}
    (hp : p ∈ probes) (hk : key ∈ [assignmentSlot p, indexSlot p, countSlot p]) :
    key ∈ registryQueries probes length := by
  simp only [registryQueries, List.mem_cons, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hk⟩))

/-- Finite observations transport through equality only at their explicit query keys. -/
theorem RegistryOn.of_read_eq {before after : LogicalStorage} {entries : List Entry}
    {probes : List B256} (h : RegistryOn before entries probes)
    (heq : ∀ key ∈ registryQueries probes entries.length, after.read key = before.read key) :
    RegistryOn after entries probes := by
  refine ⟨h.lengthLt, h.targetsNodup, h.targetsValid, h.pausersValid, h.probesValid,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq _ (mem_registryQueries_length _ _)]; exact h.lengthWord
  · intro i hi
    rw [heq _ (mem_registryQueries_array hi)]; exact h.arrayWords i hi
  · intro p hp
    rw [heq _ (mem_registryQueries_mapping hp (by simp only [List.mem_cons, List.not_mem_nil,
      or_false, true_or]))]; exact h.assignments p hp
  · intro p hp
    rw [heq _ (mem_registryQueries_mapping hp (by simp only [List.mem_cons, List.not_mem_nil,
      or_false, true_or, or_true]))]; exact h.indices p hp
  · intro p hp
    rw [heq _ (mem_registryQueries_mapping hp (by simp only [List.mem_cons, List.not_mem_nil,
      or_false, or_true]))]; exact h.counts p hp

/-- Every explicit query is within the existing decoder's observable families. -/
theorem registryQueries_observable {probes : List B256} {bound : Nat}
    (hp : ∀ p ∈ probes, canonicalAddress p) {key : B256}
    (hk : key ∈ registryQueries probes bound) : RegistryObservable bound key := by
  simp only [registryQueries, List.mem_cons, List.mem_append, or_assoc] at hk
  rcases hk with rfl | harray | hmapping
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp harray
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, List.mem_range.mp hi, rfl⟩)))
  · obtain ⟨p, hpm, hk⟩ := List.mem_flatMap.mp hmapping
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact Or.inl ⟨p, hp p hpm, rfl⟩
    · exact Or.inr (Or.inl ⟨p, hp p hpm, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, hp p hpm, rfl⟩))

/-- A raw write checked apart from exactly the finite queries preserves their agreement. -/
theorem RegistryOn.set_foreign {s : Stor} {entries : List Entry} {probes : List B256}
    {w v : B256} (h : RegistryOn (solRegistryStorage s) entries probes)
    (hapart : Blanc.SlotFootprint.checkApartOn solKey
      (registryQueries probes entries.length) [w] = true) :
    RegistryOn (solRegistryStorage (s.set w v)) entries probes := by
  apply h.of_read_eq
  intro key hk
  apply solRegistryStorage_read_congr h.lengthLt (registryQueries_observable h.probesValid hk)
  exact Stor.get_set_ne _ ((Blanc.SlotFootprint.checkApartOn_eq_true.mp hapart)
    w (by simp only [List.mem_cons, List.not_mem_nil, or_false]) key hk).symm _

/-- The raw empty storage has the finite empty-registry observation for any
finite canonical probe list. This theorem assumes no hash separation. -/
theorem registryOn_empty_raw {probes : List B256}
    (hp : ∀ p ∈ probes, canonicalAddress p) :
    RegistryOn (solRegistryStorage Stor.empty) [] probes := by
  refine ⟨by simp only [List.length_nil, Nat.reducePow, Nat.ofNat_pos], by simp only [List.map_nil, List.nodup_nil], by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true], by simp only [List.not_mem_nil, IsEmpty.forall_iff,
    implies_true], hp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [solRegistryStorage_length]; rfl
  · intro i hi; simp only [List.length_nil, List.range_zero, List.not_mem_nil] at hi
  · intro p hpm
    rw [solRegistryStorage_assignment _ _ (hp p hpm)]
    simp only [addressSlotReadWord, Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
      Std.TreeMap.getD_emptyc, assignmentAt]
    rfl
  · intro p hpm
    rw [solRegistryStorage_index _ _ (hp p hpm)]
    rfl
  · intro p hpm
    rw [solRegistryStorage_count _ _ (hp p hpm)]
    rfl

end Blanc.Lift.LidoCircuitBreakerDeployed
