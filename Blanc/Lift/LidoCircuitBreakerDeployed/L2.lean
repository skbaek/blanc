import Blanc.Lift.LidoCircuitBreakerDeployed.SetPauserRemoval
import Blanc.Lift.LidoCircuitBreakerDeployed.SetPauserFresh
import Blanc.Lift.LidoCircuitBreakerDeployed.RegistryEffects
import Blanc.Lift.LidoCircuitBreakerDeployed.Corollaries

/-!
# L2: complete removal at the deployed `setPauser(t, 0)` (entry 32)

Ladder decision D1.  L2 is the transition theorem of the actual certified
entry-32 run with arguments `(t, 0)`, concluding the actual raw storage effects:

* found target (`l2_entry32_found`, last and non-last index alike): the
  assignment and one-based index of `t` are cleared, the vacated tail's address
  field (`registryArraySlot (n - 1)`) is cleared, the length is `n - 1`, and,
  when the removed index was not the tail, the moved element (the old tail
  `sourceLastTarget entries`) sits at the hole with its index repaired.  When
  the removed index *is* the tail, hole and tail alias and the moved element is
  `t` itself (`sourceLastTarget entries = t`), which is exactly why no index
  repair is claimed there;
* absent target (`l2_entry32_absent`): the bytecode's push-then-pop leaves the
  pushed slot's address field cleared, the length unchanged, and `t`'s
  assignment and index zero.

In both cases `t` is not among the post-state witness's targets.  Every fact is
derived from the setPauser branch walks (`setPauser_removal_inv`,
`setPauser_absentZero_inv`) and RegistryLayout's raw posts; the only premise
beyond the run is the branch's own `RegistryKeysFaithful` instance.

The module also states the raw-slot form of the checkpoint premise,
`RegistryZeroRaw`, and `registryZero_of_raw`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

/-! ## The raw-slot initialization premise -/

/-- `RegistryZero` over raw Solidity slots, in the raw forms `l1_membership_raw`
and `l3_count_sum_raw` use: the array length word (slot 5) is zero, and every
canonical address has a zero assignment address field, index word and count
word. -/
def RegistryZeroRaw (s : Stor) : Prop :=
  s.get 5 = 0 ∧
  ∀ p, canonicalAddress p →
    addressSlotReadWord (s.get (mapSlot p 3)) = 0 ∧
    s.get (mapSlot p 4) = 0 ∧
    s.get (mapSlot p 6) = 0

theorem registryZero_of_raw {s : Stor} (h : RegistryZeroRaw s) : RegistryZero s := by
  refine ⟨by rw [solRegistryStorage_length]; exact h.1, fun p hp => ?_⟩
  obtain ⟨ha, hi, hc⟩ := h.2 p hp
  refine ⟨?_, ?_, ?_⟩
  · rw [solRegistryStorage_assignment _ _ hp]; exact ha
  · rw [solRegistryStorage_index _ _ hp]; exact hi
  · rw [solRegistryStorage_count _ _ hp]; exact hc

/-! ## Found target -/

/-- **L2, found target.**  A successful entry-32 run of `setPauser(t, 0)` on a
registered `t` (at `index`, among `n = entries.length`) leaves: the post-state
witness `swapPop entries index`, which does not contain `t`; `t`'s assignment
address field and index word zero; the vacated tail's address field zero; the
length word `n - 1`; when `index + 1 < n`, the moved element (the old tail)
at the hole with index `index + 1`; and when `index + 1 = n`, the moved element
is `t` (hole = tail). -/
theorem l2_entry32_found {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {target : B256} {ra : B256} {base : List B256} {post : Devm}
    {entries : List Entry} {index : Nat} {oldPauser : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = some (index, oldPauser))
    (hfaithful : RegistryKeysFaithful entries.length
      (removalWriteKeys entries target oldPauser index))
    (run : SFunc.Run prog sevm (St b (0 :: target :: 3 :: ra :: base) M G)
      t_0934_c32 (.returned post)) :
    RegistryWitness (solRegistryStorage (Devm.getStor post sevm.currentTarget))
      (swapPop entries index) ∧
    target ∉ (swapPop entries index).map Prod.fst ∧
    addressSlotReadWord ((Devm.getStor post sevm.currentTarget).get (mapSlot target 3)) = 0 ∧
    (Devm.getStor post sevm.currentTarget).get (mapSlot target 4) = 0 ∧
    addressSlotReadWord ((Devm.getStor post sevm.currentTarget).get
      (registryArraySlot (entries.length - 1))) = 0 ∧
    (Devm.getStor post sevm.currentTarget).get 5 = Nat.toB256 (entries.length - 1) ∧
    (index + 1 < entries.length →
      addressSlotReadWord ((Devm.getStor post sevm.currentTarget).get
        (registryArraySlot index)) = sourceLastTarget entries ∧
      (Devm.getStor post sevm.currentTarget).get (mapSlot (sourceLastTarget entries) 4) =
        Nat.toB256 (index + 1)) ∧
    (index + 1 = entries.length → sourceLastTarget entries = target) := by
  obtain ⟨hwrites, -, -⟩ := setPauser_removal_inv hfork hmem halign hw htarget hfind hfaithful run
  set s := Devm.getStor post sevm.currentTarget
  have hpost : RegistryWitness (solRegistryStorage s) (swapPop entries index) :=
    rawRemoval_preservesRegistry_of_registryKeysFaithful hw htarget hfind hfaithful hwrites
  have hnodup := hw.targetsNodup
  have hlt := findEntry_index_lt hfind
  have hlenLt := hw.entries_length_lt_2pow252
  obtain ⟨lastE, hlastE⟩ := last_some_of_length_pos entries (by omega)
  have hsrc : sourceLastTarget entries = lastE.1 := by
    simp only [sourceLastTarget, hlastE]
  have hpostLen := swapPop_length_of_findEntry hfind
  -- `t` is gone from the post entries.
  have hnotmem : target ∉ (swapPop entries index).map Prod.fst := by
    intro hmem'
    have hone := oneBasedIndexAt_swapPop_target_of_findEntry hfind hnodup
    have hl1 := (l1_membership_raw hpost htarget.2).2.1
    have hidx := hpost.indices target htarget.2
    rw [solRegistryStorage_index _ _ htarget.2, hone] at hidx
    exact (hl1.mpr hmem') hidx
  refine ⟨hpost, hnotmem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hpost.assignments target htarget.2
    rw [solRegistryStorage_assignment _ _ htarget.2,
      assignmentAt_swapPop_target_of_findEntry hfind hnodup] at h
    exact h
  · have h := hpost.indices target htarget.2
    rw [solRegistryStorage_index _ _ htarget.2,
      oneBasedIndexAt_swapPop_target_of_findEntry hfind hnodup] at h
    exact h
  · -- tail clear, from the raw post and two separations of the faithful premise
    have hmemLen : arrayLengthSlot ∈ removalWriteKeys entries target oldPauser index := by
      simp only [removalWriteKeys, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
    have hmemIdx : indexSlot target ∈ removalWriteKeys entries target oldPauser index := by
      simp only [removalWriteKeys, List.mem_cons, List.not_mem_nil, or_false, or_true]
    have htailKey : solKey (arrayEntrySlot (Nat.toB256 entries.length)) =
        registryArraySlot (entries.length - 1) := by
      have h := solKey_arrayEntrySlot (index := entries.length - 1) (by omega)
      rwa [show entries.length - 1 + 1 = entries.length by omega] at h
    have hobsTail : RegistryObservable entries.length
        (arrayEntrySlot (Nat.toB256 entries.length)) := by
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨entries.length - 1, by omega, ?_⟩)))
      rw [show entries.length - 1 + 1 = entries.length by omega]
    have hLb : (Nat.toB256 entries.length).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega)]
      exact hlenLt
    have h5 : registryArraySlot (entries.length - 1) ≠ 5 := by
      rw [← htailKey, ← solKey_arrayLengthSlot]
      apply solKey_ne_of_faithful hfaithful hmemLen hobsTail
      have h := arrayEntrySlot_ne_arrayLengthSlot (i := entries.length - 1) (by omega)
      rwa [show entries.length - 1 + 1 = entries.length by omega] at h
    have h4 : registryArraySlot (entries.length - 1) ≠ mapSlot target 4 := by
      rw [← htailKey, ← solKey_indexSlot htarget.2]
      apply solKey_ne_of_faithful hfaithful hmemIdx hobsTail
      exact (registryAddressFamilies_ne_arrayEntrySlot htarget.2 htarget.2 hLb).2.1.symm
    exact rawRemoval_tail_address_zero hwrites h5 h4
  · have h := hpost.lengthWord
    rw [solRegistryStorage_length, hpostLen] at h
    exact h
  · intro hnl
    have hlastValid : nonzeroCanonicalAddress lastE.1 :=
      hw.targetsValid lastE (last_mem_of_last entries hlastE)
    refine ⟨?_, ?_⟩
    · have h := hpost.arrayWords index (by omega)
      rw [solRegistryStorage_array _ _ (by omega),
        targetAt_swapPop_moved_of_lt_last entries hnl,
        targetAt_last_of_last entries hlastE] at h
      rw [h, hsrc]
    · have h := hpost.indices lastE.1 hlastValid.2
      rw [solRegistryStorage_index _ _ hlastValid.2,
        oneBasedIndexAt_swapPop_moved_of_lt_last entries hfind hnodup hlastE hnl] at h
      rw [hsrc]
      exact h
  · intro hl
    have ht := findEntry_targetAt hfind
    rw [show index = entries.length - 1 by omega, targetAt_last_of_last entries hlastE] at ht
    rw [hsrc, ht]

/-! ## Absent target -/

/-- **L2, absent target.**  A successful entry-32 run of `setPauser(t, 0)` on an
unregistered `t` keeps the witness `entries` (so `t` stays absent), leaves `t`'s
assignment address field and index word zero, clears the address field of the
slot the bytecode pushed and popped (`registryArraySlot n`), and keeps the
length word `n`. -/
theorem l2_entry32_absent {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {target : B256} {ra : B256} {base : List B256} {post : Devm}
    {entries : List Entry}
    (hfork : CoveredFork sevm.benvStat.fork) (hmem : Mem.Wf M) (halign : M.size % 32 = 0)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (htarget : nonzeroCanonicalAddress target)
    (hfind : findEntry entries target = none)
    (hfaithful : RegistryKeysFaithful (entries.length + 1)
      ((absentZeroWrites entries target).map Prod.fst))
    (run : SFunc.Run prog sevm (St b (0 :: target :: 3 :: ra :: base) M G)
      t_0934_c32 (.returned post)) :
    RegistryWitness (solRegistryStorage (Devm.getStor post sevm.currentTarget)) entries ∧
    target ∉ entries.map Prod.fst ∧
    addressSlotReadWord ((Devm.getStor post sevm.currentTarget).get (mapSlot target 3)) = 0 ∧
    (Devm.getStor post sevm.currentTarget).get (mapSlot target 4) = 0 ∧
    addressSlotReadWord ((Devm.getStor post sevm.currentTarget).get
      (registryArraySlot entries.length)) = 0 ∧
    (Devm.getStor post sevm.currentTarget).get 5 = Nat.toB256 entries.length := by
  obtain ⟨hwrites, -, -⟩ :=
    setPauser_absentZero_inv hfork hmem halign hw htarget hfind hfaithful run
  set s := Devm.getStor post sevm.currentTarget
  have hpost : RegistryWitness (solRegistryStorage s) entries :=
    rawAbsentZero_preservesRegistry hw htarget hfind hfaithful hwrites
  have hnotmem := findEntry_none_target_not_mem_targets hfind
  have hlenLt := hw.fresh_length_lt_2pow252
  have hl1 := l1_membership_raw hpost htarget.2
  refine ⟨hpost, hnotmem, ?_, ?_, ?_, ?_⟩
  · exact Classical.not_not.mp (fun h => hnotmem (hl1.1.mp h))
  · exact Classical.not_not.mp (fun h => hnotmem (hl1.2.1.mp h))
  · -- the pushed slot: the seventh write clears it, the last two miss it
    have hmemLen : arrayLengthSlot ∈ (absentZeroWrites entries target).map Prod.fst := by
      simp only [absentZeroWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false, true_or, or_true, or_self]
    have hmemIdx : indexSlot target ∈ (absentZeroWrites entries target).map Prod.fst := by
      simp only [absentZeroWrites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false, or_true, or_self]
    have hkey : solKey (arrayEntrySlot (Nat.toB256 (entries.length + 1))) =
        registryArraySlot entries.length := solKey_arrayEntrySlot hlenLt
    have hobs : RegistryObservable (entries.length + 1)
        (arrayEntrySlot (Nat.toB256 (entries.length + 1))) :=
      Or.inr (Or.inr (Or.inr (Or.inr ⟨entries.length, by omega, rfl⟩)))
    have hLb : (Nat.toB256 (entries.length + 1)).toNat < 2 ^ 252 := by
      rw [B256.toNat_toB256_of_lt (by omega)]
      exact hlenLt
    have h5 : (5 : B256) ≠ registryArraySlot entries.length := by
      rw [← hkey, ← solKey_arrayLengthSlot]
      exact (solKey_ne_of_faithful hfaithful hmemLen hobs
        (arrayEntrySlot_ne_arrayLengthSlot hlenLt)).symm
    have h4 : mapSlot target 4 ≠ registryArraySlot entries.length := by
      rw [← hkey, ← solKey_indexSlot htarget.2]
      exact (solKey_ne_of_faithful hfaithful hmemIdx hobs
        (registryAddressFamilies_ne_arrayEntrySlot htarget.2 htarget.2 hLb).2.1.symm).symm
    rw [hwrites]
    simp only [rawAbsentZeroPost, applyRegistryRawWrites, absentZeroWrites, List.foldl_cons,
      List.foldl_nil]
    rw [solKey_indexSlot htarget.2, Stor.get_set_ne _ h4, solKey_arrayLengthSlot,
      Stor.get_set_ne _ h5, hkey, Stor.get_set_self,
      registryRawValue_arrayEntrySlot hlenLt]
    exact addressSlotReadWord_write_of_clean _ _ rfl
  · have h := hpost.lengthWord
    rw [solRegistryStorage_length] at h
    exact h

end Blanc.Lift.LidoCircuitBreakerDeployed
