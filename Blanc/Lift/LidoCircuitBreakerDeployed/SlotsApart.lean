import Blanc.Lift.LidoCircuitBreakerDeployed.Writers
import Mathlib.Order.Interval.Finset.Nat

/-!
# One universal non-collision hypothesis for the deployed Lido storage layout

The history tier of the lifted CircuitBreaker carries three families of hash premises: the
per-frame `LocalApart` (the caller's `heartbeatExpiry` slot and the constant slots `0`, `1` are
off the Registry layout), the per-frame `EntryAt lidoA` (the selected `setPauser` branch's keys
are faithful and the old/new pausers' `heartbeatExpiry` slots are off the layout), and the
checkpoint premises `ForeignApart 0 0`, `ForeignApart 0 1` behind `RegistryZeroRaw`.

`LidoSlotsApart` replaces all of them by one statement about Keccak outputs: the Solidity
mapping slots `mapSlot p s = keccak(p ‖ s)` of canonical addresses `p` over the four mapping
bases `s ∈ {2, 3, 4, 6}` are pairwise distinct, miss the first `2 ^ 160` cells of the dynamic
array (`registryArraySlot i = keccak(5) + i`), and miss the fixed slots `0`, `1` and `5`.
Everything else the premises need (the array cells against each other and against the fixed
slots) is arithmetic on the concrete array base, proved here. The hypothesis is a premise:
nothing in this module discharges it.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc Blanc.LidoCircuitBreaker

/-- The deployed CircuitBreaker's Solidity mapping bases: `heartbeatExpiry` (2), and the
Registry's pauser (3), index (4) and count (6) mappings. -/
def mappingBases : List B256 := [2, 3, 4, 6]

/-- **The one universal non-collision hypothesis** of the deployed CircuitBreaker's storage
layout: Keccak is injective on the mapping slots of canonical addresses over `mappingBases`,
and those slots miss the first `2 ^ 160` dynamic-array cells and the fixed slots `0`, `1`, `5`.
A statement about Keccak outputs, not a fact the model can decide. -/
structure LidoSlotsApart : Prop where
  injective : ∀ {p q s s' : B256}, canonicalAddress p → canonicalAddress q →
    s ∈ mappingBases → s' ∈ mappingBases → mapSlot p s = mapSlot q s' → p = q ∧ s = s'
  offArray : ∀ {p s : B256} {i : Nat}, canonicalAddress p → s ∈ mappingBases →
    i < 2 ^ 160 → mapSlot p s ≠ registryArraySlot i
  offFixed : ∀ {p s : B256}, canonicalAddress p → s ∈ mappingBases →
    mapSlot p s ≠ 0 ∧ mapSlot p s ≠ 1 ∧ mapSlot p s ≠ 5

/-! ## The concrete array base -/

/-- The dynamic array's data base `keccak(5)`, by kernel evaluation. -/
theorem registryArrayBase_eq :
    registryArrayBase = 0x36b6384b5eca791c62761152d0c79bb0604c104a5fb6f4eb0703f3154bb3db0 := by
  decide +kernel

theorem registryArrayBase_toNat :
    registryArrayBase.toNat = 0x36b6384b5eca791c62761152d0c79bb0604c104a5fb6f4eb0703f3154bb3db0 := by
  rw [registryArrayBase_eq]
  decide +kernel

/-- The first `2 ^ 160` array cells do not wrap. -/
theorem registryArraySlot_toNat {i : Nat} (hi : i < 2 ^ 160) :
    (registryArraySlot i).toNat = registryArrayBase.toNat + i := by
  have hi' : (Nat.toB256 i).toNat = i := B256.toNat_toB256_of_lt (by omega)
  unfold registryArraySlot
  rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; rw [hi', registryArrayBase_toNat]; omega),
    hi']

theorem registryArraySlot_inj {i j : Nat} (hi : i < 2 ^ 160) (hj : j < 2 ^ 160)
    (h : registryArraySlot i = registryArraySlot j) : i = j := by
  have := congrArg B256.toNat h
  rw [registryArraySlot_toNat hi, registryArraySlot_toNat hj] at this
  omega

theorem registryArraySlot_ne_small {i : Nat} (hi : i < 2 ^ 160) {w : B256}
    (hw : w.toNat < 2 ^ 249) : registryArraySlot i ≠ w := by
  intro h
  have := congrArg B256.toNat h
  rw [registryArraySlot_toNat hi, registryArrayBase_toNat] at this
  omega

theorem registryArraySlot_ne_fixed {i : Nat} (hi : i < 2 ^ 160) :
    registryArraySlot i ≠ 0 ∧ registryArraySlot i ≠ 1 ∧ registryArraySlot i ≠ 5 :=
  ⟨registryArraySlot_ne_small hi (by decide), registryArraySlot_ne_small hi (by decide),
    registryArraySlot_ne_small hi (by decide)⟩

/-! ## Observable keys and their raw slots -/

private theorem mem_mappingBases_2 : (2 : B256) ∈ mappingBases := by
  simp only [mappingBases, List.mem_cons, List.not_mem_nil, or_false, true_or]
private theorem mem_mappingBases_3 : (3 : B256) ∈ mappingBases := by
  simp only [mappingBases, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
private theorem mem_mappingBases_4 : (4 : B256) ∈ mappingBases := by
  simp only [mappingBases, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
private theorem mem_mappingBases_6 : (6 : B256) ∈ mappingBases := by
  simp only [mappingBases, List.mem_cons, List.not_mem_nil, or_false, or_true]

/-- The Registry's own mapping bases (pauser, index, count). -/
private def registryBases : List B256 := [3, 4, 6]

private theorem mappingBases_of_registryBases {s : B256} (hs : s ∈ registryBases) :
    s ∈ mappingBases := by
  simp only [registryBases, mappingBases, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
  rcases hs with rfl | rfl | rfl <;> simp only [true_or, or_true]

/-- The raw slot of an observable logical key, by family. -/
private inductive RawKind : B256 → Prop
  | mapping {p s : B256} : canonicalAddress p → s ∈ registryBases → RawKind (mapSlot p s)
  | length : RawKind 5
  | array {i : Nat} : i < 2 ^ 160 → RawKind (registryArraySlot i)

private theorem rawKind_of_observable {k : B256} (hk : RegistryObservable (2 ^ 160) k) :
    RawKind (solKey k) := by
  rcases hk with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | rfl | ⟨i, hi, rfl⟩
  · rw [solKey_assignmentSlot hp]; exact .mapping hp (by simp only [registryBases,
      List.mem_cons, List.not_mem_nil, or_false, true_or])
  · rw [solKey_indexSlot hp]; exact .mapping hp (by simp only [registryBases,
      List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])
  · rw [solKey_countSlot hp]; exact .mapping hp (by simp only [registryBases,
      List.mem_cons, List.not_mem_nil, or_false, or_true])
  · rw [solKey_arrayLengthSlot]; exact .length
  · rw [solKey_arrayEntrySlot (by omega)]; exact .array hi

/-- An observable key, with its family and raw slot. -/
private theorem observable_cases {k : B256} (hk : RegistryObservable (2 ^ 160) k) :
    (∃ p, canonicalAddress p ∧ ∃ s ∈ registryBases, solKey k = mapSlot p s ∧
      k = (if s = 3 then assignmentSlot p else if s = 4 then indexSlot p else countSlot p)) ∨
    (k = arrayLengthSlot ∧ solKey k = 5) ∨
    (∃ i, i < 2 ^ 160 ∧ k = arrayEntrySlot (Nat.toB256 (i + 1)) ∧
      solKey k = registryArraySlot i) := by
  rcases hk with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | rfl | ⟨i, hi, rfl⟩
  · exact Or.inl ⟨p, hp, 3, by simp only [registryBases, List.mem_cons, List.not_mem_nil,
      or_false, true_or], solKey_assignmentSlot hp, by simp only [↓reduceIte]⟩
  · exact Or.inl ⟨p, hp, 4, by simp only [registryBases, List.mem_cons, List.not_mem_nil,
      or_false, true_or, or_true], solKey_indexSlot hp, by
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_left_of_eq_true _ _ (eq_true rfl)]⟩
  · exact Or.inl ⟨p, hp, 6, by simp only [registryBases, List.mem_cons, List.not_mem_nil,
      or_false, or_true], solKey_countSlot hp, by rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_right_of_eq_false _ _ (eq_false (by decide))]⟩
  · exact Or.inr (Or.inl ⟨rfl, solKey_arrayLengthSlot⟩)
  · exact Or.inr (Or.inr ⟨i, hi, rfl, solKey_arrayEntrySlot (by omega)⟩)

namespace LidoSlotsApart

variable (H : LidoSlotsApart)
include H

/-- Under the hypothesis, `solKey` is injective on the keys a `RegistryWitness` observes
within the `2 ^ 160` array bound. -/
theorem solKey_inj {k t : B256} (hk : RegistryObservable (2 ^ 160) k)
    (ht : RegistryObservable (2 ^ 160) t) (h : solKey k = solKey t) : k = t := by
  rcases observable_cases hk with ⟨p, hp, s, hs, hks, rfl⟩ | ⟨rfl, hks⟩ | ⟨i, hi, rfl, hks⟩ <;>
  rcases observable_cases ht with ⟨q, hq, s', hs', hts, rfl⟩ | ⟨rfl, hts⟩ | ⟨j, hj, rfl, hts⟩ <;>
  replace h := hks.symm.trans (h.trans hts)
  · obtain ⟨rfl, rfl⟩ := H.injective hp hq (mappingBases_of_registryBases hs)
      (mappingBases_of_registryBases hs') h
    rfl
  · exact absurd h (H.offFixed hp (mappingBases_of_registryBases hs)).2.2
  · exact absurd h (H.offArray hp (mappingBases_of_registryBases hs) hj)
  · exact absurd h.symm (H.offFixed hq (mappingBases_of_registryBases hs')).2.2
  · rfl
  · exact absurd h.symm (registryArraySlot_ne_fixed hj).2.2
  · exact absurd h.symm (H.offArray hq (mappingBases_of_registryBases hs') hi)
  · exact absurd h (registryArraySlot_ne_fixed hi).2.2
  · obtain rfl := registryArraySlot_inj hi hj h
    rfl

/-- Faithfulness of every written-key list whose keys are observable within the bound. -/
theorem faithful {T : List B256} (hT : ∀ t ∈ T, RegistryObservable (2 ^ 160) t) :
    RegistryKeysFaithful (2 ^ 160) T :=
  fun t ht _ hk heq => H.solKey_inj hk (hT t ht) heq

/-- A raw slot of one of the three classified kinds is off every observable key's slot
unless it is that key's slot; for a `heartbeatExpiry` slot that never happens. -/
theorem foreignApart_expiry {c : B256} (hc : canonicalAddress c) :
    ForeignApart (2 ^ 160) (mapSlot c 2) := by
  intro k hk heq
  have hr := rawKind_of_observable hk
  generalize solKey k = r at hr heq
  cases hr with
  | mapping hp hs =>
      have h2 := (H.injective hp hc (mappingBases_of_registryBases hs) mem_mappingBases_2 heq).2
      subst h2
      simp only [registryBases, List.mem_cons, List.not_mem_nil, or_false] at hs
      revert hs
      decide
  | length => exact (H.offFixed hc mem_mappingBases_2).2.2 heq.symm
  | array hi => exact H.offArray hc mem_mappingBases_2 hi heq.symm

/-- The constant slots `0` and `1` are off every observable key's slot. -/
theorem foreignApart_fixed {w : B256} (hw : w = 0 ∨ w = 1) {bound : Nat}
    (hb : bound ≤ 2 ^ 160) : ForeignApart bound w := by
  intro k hk heq
  have hr := rawKind_of_observable (hk.mono hb)
  generalize solKey k = r at hr heq
  cases hr with
  | mapping hp hs =>
      rcases hw with rfl | rfl
      · exact (H.offFixed hp (mappingBases_of_registryBases hs)).1 heq
      · exact (H.offFixed hp (mappingBases_of_registryBases hs)).2.1 heq
  | length => rcases hw with rfl | rfl <;> exact absurd heq (by decide)
  | array hi =>
      rcases hw with rfl | rfl
      · exact (registryArraySlot_ne_fixed hi).1 heq
      · exact (registryArraySlot_ne_fixed hi).2.1 heq

end LidoSlotsApart

/-! ## The written keys of every `setPauser` branch are observable -/

private theorem obs_assign {p : B256} (hp : canonicalAddress p) :
    RegistryObservable (2 ^ 160) (assignmentSlot p) := Or.inl ⟨p, hp, rfl⟩
private theorem obs_index {p : B256} (hp : canonicalAddress p) :
    RegistryObservable (2 ^ 160) (indexSlot p) := Or.inr (Or.inl ⟨p, hp, rfl⟩)
private theorem obs_count {p : B256} (hp : canonicalAddress p) :
    RegistryObservable (2 ^ 160) (countSlot p) := Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))
private theorem obs_length : RegistryObservable (2 ^ 160) arrayLengthSlot :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))
private theorem obs_array {i : Nat} (hi : i < 2 ^ 160) :
    RegistryObservable (2 ^ 160) (arrayEntrySlot (Nat.toB256 (i + 1))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))

/-- A list of distinct nonzero canonical addresses has fewer than `2 ^ 160` members. -/
theorem length_lt_of_nodup_canonical {l : List B256} (hnodup : l.Nodup)
    (hvalid : ∀ x ∈ l, nonzeroCanonicalAddress x) : l.length < 2 ^ 160 := by
  have hinj : (l.map B256.toNat).Nodup :=
    hnodup.map (fun a b h => B256.toNat_inj a b h)
  have hsub : (l.map B256.toNat).toFinset ⊆ Finset.Ico 1 (2 ^ 160) := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
    obtain ⟨hne, hcan⟩ := hvalid x hx
    have hpos : x.toNat ≠ 0 := fun h0 => hne (B256.toNat_inj _ _ (by rw [h0]; rfl))
    exact Finset.mem_Ico.mpr ⟨Nat.pos_of_ne_zero hpos, hcan⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hinj, List.length_map, Nat.card_Ico] at hcard
  omega

private theorem mem_of_last? {entries : List Entry} {e : Entry} (h : last? entries = some e) :
    e ∈ entries := by
  induction entries with
  | nil => simp only [last?, reduceCtorEq] at h
  | cons head rest ih =>
      cases rest with
      | nil =>
          simp only [last?, Option.some.injEq] at h
          subst h
          exact List.mem_singleton_self _
      | cons next tail =>
          exact List.mem_cons_of_mem _ (ih (by simpa only [last?] using h))

private theorem canonical_sourceLastTarget {entries : List Entry}
    (hvalid : ∀ e ∈ entries, nonzeroCanonicalAddress e.1) :
    canonicalAddress (sourceLastTarget entries) := by
  unfold sourceLastTarget
  cases hlast : last? entries with
  | none => unfold canonicalAddress; decide
  | some e => exact (hvalid e (mem_of_last? hlast)).2

/-- Every key of the branch `setPauser(t, np)` selects is observable within the bound, for
canonical `t`, `np` and a witness of the frame-entry storage. -/
theorem setPauserKeys_observable {s : Stor} {entries : List Entry} {t np : B256}
    (hw : RegistryWitness (solRegistryStorage s) entries)
    (ht : canonicalAddress t) (hnp : canonicalAddress np) :
    ∀ k ∈ setPauserKeys entries t np, RegistryObservable (2 ^ 160) k := by
  have hlen : entries.length < 2 ^ 160 := by
    have h := length_lt_of_nodup_canonical hw.targetsNodup (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact hw.targetsValid e he)
    rwa [List.length_map] at h
  unfold setPauserKeys
  cases hf : findEntry entries t with
  | some found =>
      obtain ⟨index, old⟩ := found
      have hidx := findEntry_index_lt hf
      have hold : canonicalAddress old := (hw.pausersValid _ (mem_of_findEntry hf)).2
      by_cases hz : np = 0
      · simp only [hz, ↓reduceIte, removalWriteKeys, List.mem_cons, List.not_mem_nil, or_false]
        have hlast : arrayEntrySlot (Nat.toB256 entries.length) =
            arrayEntrySlot (Nat.toB256 (entries.length - 1 + 1)) := by
          rw [Nat.sub_add_cancel (by omega)]
        rintro k (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · exact obs_assign ht
        · exact obs_count hold
        · exact obs_array (by omega)
        · exact obs_index (canonical_sourceLastTarget hw.targetsValid)
        · rw [hlast]; exact obs_array (by omega)
        · exact obs_length
        · exact obs_index ht
      · simp only [hz, ↓reduceIte, nonzeroWrites, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false]
        rintro k (rfl | rfl | rfl)
        · exact obs_assign ht
        · exact obs_count hold
        · exact obs_count hnp
  | none =>
      by_cases hz : np = 0
      · simp only [hz, ↓reduceIte, absentZeroWrites, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · exact obs_assign ht
        · exact obs_array hlen
        · exact obs_index ht
        · exact obs_length
        · exact obs_array hlen
        · exact obs_index ht
        · exact obs_array hlen
        · exact obs_length
        · exact obs_index ht
      · simp only [hz, ↓reduceIte, freshWriteKeys, List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl | rfl | rfl | rfl)
        · exact obs_assign ht
        · exact obs_array hlen
        · exact obs_index ht
        · exact obs_length
        · exact obs_count hnp

namespace LidoSlotsApart

variable (H : LidoSlotsApart)
include H

/-- The concrete Registry-writer premise `lidoA` holds over every witness. -/
theorem lidoA_of_witness {s : Stor} {entries : List Entry} {sevm : Sevm}
    (hw : RegistryWitness (solRegistryStorage s) entries) : lidoA entries sevm := by
  refine ⟨fun ht hnp => ⟨H.faithful (setPauserKeys_observable hw ht.2 hnp), ?_, ?_⟩,
    fun ht => H.faithful (setPauserKeys_observable hw ht.2 (by unfold canonicalAddress; decide))⟩
  · intro hne
    cases hf : findEntry entries (Sevm.dataWord sevm 4) with
    | none => exact absurd (findEntry_none_assignmentAt hf) hne
    | some found =>
        obtain ⟨index, old⟩ := found
        rw [findEntry_assignmentAt hf]
        exact H.foreignApart_expiry (hw.pausersValid _ (mem_of_findEntry hf)).2
  · intro _
    exact H.foreignApart_expiry hnp

/-- **Every frame entry condition of the history tier** follows from the one hypothesis. -/
theorem lidoEntry (sevm : Sevm) (d : Devm) :
    LidoCircuitBreakerDeployed.lidoEntry lidoA sevm d := by
  refine ⟨⟨?_, H.foreignApart_fixed (Or.inl rfl) le_rfl, H.foreignApart_fixed (Or.inr rfl) le_rfl⟩,
    fun _ hw => H.lidoA_of_witness hw⟩
  rw [← toAdr_toB256 sevm.caller]
  exact H.foreignApart_expiry (canonical_toAdr_toB256 _)

end LidoSlotsApart

end Blanc.Lift.LidoCircuitBreakerDeployed
