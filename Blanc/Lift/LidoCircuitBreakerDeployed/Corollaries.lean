import Blanc.Lift.LidoCircuitBreakerDeployed.RegistryLayout
import Blanc.Lift.LidoCircuitBreakerDeployed.Contract
import Blanc.Lift.LidoCircuitBreakerDeployed.Frame
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Deployed Lido CircuitBreaker Registry corollaries and RegistryZero start

Ladder unit (g). Corollaries of `RegistryWitness` under the deployed Solidity
storage projection `solRegistryStorage`:

1. `l1_membership`: logical membership equivalence for canonical targets, with
   assignment, index, and array slot pinning for found entries.
   `l1_membership_raw`: the same rewritten to raw storage reads.
2. `l3_count_sum`: logical count conservation and live pauser count sum.
   `l3_count_sum_raw`: the same rewritten to raw storage reads.
3. `RegistryZero`: the logical zero storage state, and `inv_of_registryZero`
   providing an empty witness `[]`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker
open scoped BigOperators

abbrev Entry := LidoCircuitBreaker.Entry

theorem assignmentCount_eq_count_map
    (entries : List Entry) (pauser : B256) :
    assignmentCount entries pauser = (entries.map Prod.snd).count pauser := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [assignmentCount, List.map_cons, List.count_cons, ih]
      by_cases h : entry.2 = pauser
      · subst h
        simp only [↓reduceIte, BEq.rfl, Nat.add_comm]
      · simp only [h, ↓reduceIte, zero_add, beq_iff_eq, add_zero]

/-- **L1 logical membership**: for canonical target `t`, assignment and index
reads are nonzero iff `t` is registered, and a found entry pins the assignment,
one-based index, and array entry word. -/
theorem l1_membership {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (solRegistryStorage s) entries)
    {t : B256} (ht : canonicalAddress t) :
    ((solRegistryStorage s).read (assignmentSlot t) ≠ 0 ↔
      t ∈ entries.map Prod.fst) ∧
    ((solRegistryStorage s).read (indexSlot t) ≠ 0 ↔
      t ∈ entries.map Prod.fst) ∧
    ∀ index pauser, findEntry entries t = some (index, pauser) →
      (solRegistryStorage s).read (assignmentSlot t) = pauser ∧
      (solRegistryStorage s).read (indexSlot t) =
        Nat.toB256 (index + 1) ∧
      (solRegistryStorage s).read (arrayEntrySlot (Nat.toB256 (index + 1))) = t := by
  have hassignment :
      (solRegistryStorage s).read (assignmentSlot t) =
        assignmentAt entries t :=
    hw.assignments t ht
  have hindex :
      (solRegistryStorage s).read (indexSlot t) =
        Nat.toB256 (oneBasedIndexAt entries t) :=
    hw.indices t ht
  cases hfind : findEntry entries t with
  | none =>
      have hnotmem := findEntry_none_target_not_mem_targets hfind
      have hassignmentZero := findEntry_none_assignmentAt hfind
      have hindexZero := findEntry_none_oneBasedIndexAt hfind
      refine ⟨?_, ?_, ?_⟩
      · constructor
        · intro hne
          apply (hne _).elim
          rw [hassignment, hassignmentZero]
        · intro hmem
          exact (hnotmem hmem).elim
      · constructor
        · intro hne
          apply (hne _).elim
          rw [hindex, hindexZero]
          rfl
        · intro hmem
          exact (hnotmem hmem).elim
      · intro index pauser hsome
        contradiction
  | some found =>
      obtain ⟨foundIndex, foundPauser⟩ := found
      have hentry : (t, foundPauser) ∈ entries :=
        mem_of_findEntry hfind
      have hmem : t ∈ entries.map Prod.fst :=
        List.mem_map.mpr ⟨(t, foundPauser), hentry, rfl⟩
      have hpauserNe : foundPauser ≠ 0 :=
        (hw.pausersValid (t, foundPauser) hentry).1
      have hassignmentFound := findEntry_assignmentAt hfind
      have hindexFound := findEntry_oneBasedIndexAt hfind
      have hassignmentNe :
          (solRegistryStorage s).read (assignmentSlot t) ≠ 0 := by
        rw [hassignment, hassignmentFound]
        exact hpauserNe
      have hfoundLt := findEntry_index_lt hfind
      have hindexBound : foundIndex + 1 < 2 ^ 256 := by
        have hlengthLt := hw.entries_length_lt_2pow256
        omega
      have hindexNe :
          (solRegistryStorage s).read (indexSlot t) ≠ 0 := by
        rw [hindex, hindexFound]
        intro hzero
        have hnat := congrArg B256.toNat hzero
        rw [B256.toNat_toB256_of_lt hindexBound,
          B256.toNat_zero] at hnat
        omega
      refine ⟨⟨fun _ => hmem, fun _ => hassignmentNe⟩,
        ⟨fun _ => hmem, fun _ => hindexNe⟩, ?_⟩
      intro index pauser hlookup
      cases hlookup
      refine ⟨?_, ?_, ?_⟩
      · exact hassignment.trans hassignmentFound
      · exact hindex.trans (congrArg Nat.toB256 hindexFound)
      · rw [hw.arrayWords foundIndex hfoundLt, findEntry_targetAt hfind]

/-- **L1 raw membership**: the raw Solidity storage counterpart of `l1_membership`,
with reads rewritten via the `solRegistryStorage` lemmas. -/
theorem l1_membership_raw {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (solRegistryStorage s) entries)
    {t : B256} (ht : canonicalAddress t) :
    (addressSlotReadWord (s.get (mapSlot t 3)) ≠ 0 ↔
      t ∈ entries.map Prod.fst) ∧
    (s.get (mapSlot t 4) ≠ 0 ↔
      t ∈ entries.map Prod.fst) ∧
    ∀ index pauser, findEntry entries t = some (index, pauser) →
      addressSlotReadWord (s.get (mapSlot t 3)) = pauser ∧
      s.get (mapSlot t 4) = Nat.toB256 (index + 1) ∧
      addressSlotReadWord (s.get (registryArraySlot index)) = t := by
  have hl1 := l1_membership hw ht
  rw [solRegistryStorage_assignment s t ht] at hl1
  rw [solRegistryStorage_index s t ht] at hl1
  refine ⟨hl1.1, hl1.2.1, ?_⟩
  intro index pauser hfind
  have hspec := hl1.2.2 index pauser hfind
  have hbound : index + 1 < 2 ^ 252 := by
    have hlt := findEntry_index_lt hfind
    have hlen := hw.entries_length_lt_2pow252
    omega
  rw [solRegistryStorage_array s index hbound] at hspec
  exact hspec

/-- **L3 logical count conservation**: counts agree with `assignmentCount entries`,
the zero-pauser count is 0, and the sum of counts over live pausers equals array length. -/
theorem l3_count_sum {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (solRegistryStorage s) entries) :
    (∀ p, canonicalAddress p →
      (solRegistryStorage s).read (countSlot p) =
        Nat.toB256 (assignmentCount entries p)) ∧
    (solRegistryStorage s).read (countSlot 0) = 0 ∧
    (∑ p ∈ (entries.map Prod.snd).toFinset,
      ((solRegistryStorage s).read (countSlot p)).toNat) =
        entries.length := by
  refine ⟨hw.counts, hw.zeroCount, ?_⟩
  calc
    (∑ p ∈ (entries.map Prod.snd).toFinset,
      ((solRegistryStorage s).read (countSlot p)).toNat) =
        ∑ p ∈ (entries.map Prod.snd).toFinset,
          assignmentCount entries p := by
            apply Finset.sum_congr rfl
            intro p hp
            have hpMem : p ∈ entries.map Prod.snd := by
              simpa only [List.mem_map, Prod.exists, exists_eq_right, List.mem_toFinset] using hp
            obtain ⟨entry, hentry, hpEq⟩ := List.mem_map.mp hpMem
            have hcanonical : canonicalAddress p := by
              rw [← hpEq]
              exact (hw.pausersValid entry hentry).2
            have hcount := hw.counts p hcanonical
            rw [hcount, B256.toNat_toB256_of_lt (hw.assignmentCount_lt_2pow256 p)]
    _ = ∑ p ∈ (entries.map Prod.snd).toFinset,
          (entries.map Prod.snd).count p := by
            apply Finset.sum_congr rfl
            intro p _
            exact assignmentCount_eq_count_map entries p
    _ = entries.length := by
            rw [List.sum_toFinset_count_eq_length]
            simp only [List.length_map]

/-- **L3 raw count conservation**: the raw Solidity storage counterpart of `l3_count_sum`,
with count reads rewritten to slot `mapSlot p 6`. -/
theorem l3_count_sum_raw {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (solRegistryStorage s) entries) :
    (∀ p, canonicalAddress p →
      s.get (mapSlot p 6) = Nat.toB256 (assignmentCount entries p)) ∧
    s.get (mapSlot 0 6) = 0 ∧
    (∑ p ∈ (entries.map Prod.snd).toFinset,
      (s.get (mapSlot p 6)).toNat) = entries.length := by
  have hl3 := l3_count_sum hw
  have hzero_can : canonicalAddress 0 := by
    unfold canonicalAddress
    change (0 : Nat) < 2 ^ 160
    norm_num
  have hcount_raw : ∀ p, canonicalAddress p →
      s.get (mapSlot p 6) = Nat.toB256 (assignmentCount entries p) := by
    intro p hp
    rw [← solRegistryStorage_count s p hp]
    exact hl3.1 p hp
  have hzero_raw : s.get (mapSlot 0 6) = 0 := by
    rw [← solRegistryStorage_count s 0 hzero_can]
    exact hl3.2.1
  refine ⟨hcount_raw, hzero_raw, ?_⟩
  calc
    (∑ p ∈ (entries.map Prod.snd).toFinset, (s.get (mapSlot p 6)).toNat) =
      ∑ p ∈ (entries.map Prod.snd).toFinset,
        ((solRegistryStorage s).read (countSlot p)).toNat := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpMem : p ∈ entries.map Prod.snd := by
            simpa only [List.mem_map, Prod.exists, exists_eq_right, List.mem_toFinset] using hp
          obtain ⟨entry, hentry, hpEq⟩ := List.mem_map.mp hpMem
          have hcanonical : canonicalAddress p := by
            rw [← hpEq]
            exact (hw.pausersValid entry hentry).2
          rw [solRegistryStorage_count s p hcanonical]
    _ = entries.length := hl3.2.2

/-- The storage `s` exhibits the logical zero Registry state: array length is 0,
and every canonical address has 0 assignment, index, and count. -/
def RegistryZero (s : Stor) : Prop :=
  (solRegistryStorage s).read arrayLengthSlot = 0 ∧
  ∀ p, canonicalAddress p →
    (solRegistryStorage s).read (assignmentSlot p) = 0 ∧
    (solRegistryStorage s).read (indexSlot p) = 0 ∧
    (solRegistryStorage s).read (countSlot p) = 0

/-- A storage satisfying `RegistryZero` admits a Registry witness with empty
entries `[]`, satisfying the contract state invariant. -/
theorem inv_of_registryZero {s : Stor} (h : RegistryZero s) :
    ∃ entries, RegistryWitness (solRegistryStorage s) entries := by
  refine ⟨[], ?_⟩
  refine ⟨by simp only [List.map_nil, List.nodup_nil], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entry hentry; simp only [List.not_mem_nil] at hentry
  · intro entry hentry; simp only [List.not_mem_nil] at hentry
  · exact h.1
  · intro index hindex; simp only [List.length_nil, not_lt_zero] at hindex
  · intro target htarget; exact (h.2 target htarget).1
  · intro target htarget; exact (h.2 target htarget).2.1
  · intro pauser hpauser; exact (h.2 pauser hpauser).2.2
  · have h0 : canonicalAddress 0 := by
      unfold canonicalAddress
      change (0 : Nat) < 2 ^ 160
      norm_num
    exact (h.2 0 h0).2.2


end Blanc.Lift.LidoCircuitBreakerDeployed
