import Blanc.Lift.LidoCircuitBreakerDeployed.Corollaries

/-!
# The CircuitBreaker Registry read directly from storage

Short observers of the deployed CircuitBreaker's raw storage: the stored target array
(`registeredTargets`, slot `5` and the array cells `keccak(5) + i`), each target's pauser
(`pauserOf`, mapping `3`) and one-based index (`indexOf`, mapping `4`), and each pauser's guard
count (`guardCount`, mapping `6`). The public headlines state two named Props over them:

* `ConsistentRegistry s`: the stored registry is internally consistent;
* `RemovalRepaired pre post t`: the stored registry after removing `t` is the one before it
  with `t` swap-and-popped out.

Neither statement mentions an entry list or a model state. The rest of this file proves each
from a `RegistryWitness` of the raw storage, which is how the history theorems supply them.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc Blanc.LidoCircuitBreaker

/-! ## Observers -/

/-- The stored target array: the length word (slot `5`) and that many array cells, each read as
an address. -/
def registeredTargets (s : Stor) : List B256 :=
  (List.range (s.get 5).toNat).map fun i => addressSlotReadWord (s.get (registryArraySlot i))

/-- The pauser stored for target `t` (mapping slot `3`), read as an address. -/
def pauserOf (s : Stor) (t : B256) : B256 := addressSlotReadWord (s.get (mapSlot t 3))

/-- The one-based array index stored for target `t` (mapping slot `4`); zero means absent. -/
def indexOf (s : Stor) (t : B256) : B256 := s.get (mapSlot t 4)

/-- The number of targets stored as guarded by pauser `p` (mapping slot `6`). -/
def guardCount (s : Stor) (p : B256) : B256 := s.get (mapSlot p 6)

/-- **The stored Registry is consistent.** The stored targets are distinct; a target has a
nonzero pauser and a nonzero index exactly when it is stored in the array; each stored
target's index is its array position plus one; each pauser's guard count is the number of
stored targets whose pauser it is; and the zero address guards nothing. -/
def ConsistentRegistry (s : Stor) : Prop :=
  (registeredTargets s).Nodup ∧
  (∀ t, canonicalAddress t →
    (pauserOf s t ≠ 0 ↔ t ∈ registeredTargets s) ∧
    (indexOf s t ≠ 0 ↔ t ∈ registeredTargets s)) ∧
  (∀ i (h : i < (registeredTargets s).length),
    indexOf s (registeredTargets s)[i] = Nat.toB256 (i + 1)) ∧
  (∀ p, canonicalAddress p →
    guardCount s p = Nat.toB256 ((registeredTargets s).countP (fun t => pauserOf s t = p))) ∧
  guardCount s 0 = 0

/-- Swap-and-pop on a target list: overwrite position `i` with the last target, then drop the
last position. -/
def targetsSwapPop (ts : List B256) (i : Nat) : List B256 :=
  match ts.getLast? with
  | none => ts
  | some last => (ts.set i last).dropLast

/-- **Removal of `t` repairs the stored Registry.** After the removal, `t` has no pauser and no
index, and the stored target array is the one before it with `t` swap-and-popped out (unchanged
when `t` was not stored). -/
def RemovalRepaired (pre post : Stor) (t : B256) : Prop :=
  pauserOf post t = 0 ∧ indexOf post t = 0 ∧
  registeredTargets post =
    if t ∈ registeredTargets pre then
      targetsSwapPop (registeredTargets pre) ((registeredTargets pre).idxOf t)
    else registeredTargets pre

/-- The entry list a `setPauser(t, 0)` call leaves: `t` swap-and-popped out when found, and the
list unchanged otherwise. -/
def removedEntries (entries : List Entry) (t : B256) : List Entry :=
  match findEntry entries t with
  | some (index, _) => swapPop entries index
  | none => entries

/-! ## Entry-list facts -/

private theorem targetAt_eq_getElem (entries : List Entry) {i : Nat} (h : i < entries.length) :
    targetAt entries i = (entries[i]'h).1 := by
  induction entries generalizing i with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at h
  | cons entry rest ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih (Nat.lt_of_succ_lt_succ h)

/-- In a list with distinct targets, the entry at position `i` is found at `i`. -/
private theorem findEntry_getElem (entries : List Entry)
    (hnodup : (entries.map Prod.fst).Nodup) {i : Nat} (h : i < entries.length) :
    findEntry entries (entries[i]'h).1 = some (i, (entries[i]'h).2) := by
  induction entries generalizing i with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at h
  | cons entry rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      cases i with
      | zero => simp only [findEntry, List.getElem_cons_zero, ↓reduceIte]
      | succ i =>
          have hi := Nat.lt_of_succ_lt_succ h
          have hne : entry.1 ≠ (rest[i]'hi).1 := fun heq =>
            hnodup.1 (heq ▸ List.mem_map.mpr ⟨rest[i]'hi, List.getElem_mem hi, rfl⟩)
          simp only [findEntry, List.getElem_cons_succ, hne, ↓reduceIte, ih hnodup.2 hi]

private theorem idxOf_of_findEntry {entries : List Entry} {t : B256} {index : Nat}
    {pauser : B256} (h : findEntry entries t = some (index, pauser)) :
    (entries.map Prod.fst).idxOf t = index := by
  induction entries generalizing index pauser with
  | nil => simp only [findEntry, reduceCtorEq] at h
  | cons entry rest ih =>
      rw [List.map_cons, List.idxOf_cons]
      by_cases heq : entry.1 = t
      · simp only [findEntry, heq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [heq, BEq.rfl, ↓reduceIte]
      · have hb : (entry.1 == t) = false := beq_false_of_ne heq
        cases hf : findEntry rest t with
        | none => simp only [findEntry, heq, ↓reduceIte, hf, reduceCtorEq] at h
        | some found =>
            obtain ⟨fi, fp⟩ := found
            simp only [findEntry, heq, ↓reduceIte, hf, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            simp only [hb, Bool.false_eq_true, ↓reduceIte, ih hf]

private theorem map_fst_setEntryAt (entries : List Entry) (i : Nat) (e : Entry) :
    (setEntryAt i e entries).map Prod.fst = (entries.map Prod.fst).set i e.1 := by
  induction entries generalizing i with
  | nil => cases i <;> rfl
  | cons head rest ih =>
      cases i with
      | zero => rfl
      | succ i => simp only [setEntryAt, List.map_cons, List.set_cons_succ, ih]

private theorem map_fst_dropLast (entries : List Entry) :
    (dropLast entries).map Prod.fst = (entries.map Prod.fst).dropLast := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          change (head :: dropLast (next :: tail)).map Prod.fst = _
          rw [List.map_cons, ih]
          rfl

private theorem getLast?_map_fst (entries : List Entry) :
    (entries.map Prod.fst).getLast? = (last? entries).map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          rw [List.map_cons, List.map_cons, List.getLast?_cons_cons, ← List.map_cons, ih]
          rfl

private theorem map_fst_swapPop (entries : List Entry) (i : Nat) :
    (swapPop entries i).map Prod.fst = targetsSwapPop (entries.map Prod.fst) i := by
  unfold targetsSwapPop
  rw [getLast?_map_fst]
  cases h : last? entries with
  | none => simp only [swapPop, h, Option.map_none]
  | some last => simp only [swapPop, h, Option.map_some, map_fst_dropLast, map_fst_setEntryAt]

/-! ## From a Registry witness to the observers -/

variable {s : Stor} {entries : List Entry}

/-- A Registry witness's targets are exactly the stored target array. -/
theorem registeredTargets_eq (hw : RegistryWitness (solRegistryStorage s) entries) :
    registeredTargets s = entries.map Prod.fst := by
  have hbound := hw.entries_length_lt_2pow252
  have hlen := hw.lengthWord
  rw [solRegistryStorage_length] at hlen
  have hn : (s.get 5).toNat = entries.length := by
    rw [hlen]
    exact B256.toNat_toB256_of_lt (by omega)
  apply List.ext_getElem
  · simp only [registeredTargets, List.length_map, List.length_range, hn]
  · intro i h1 _
    have hi : i < entries.length := by
      simpa only [registeredTargets, List.length_map, List.length_range, hn] using h1
    simp only [registeredTargets, List.getElem_map, List.getElem_range]
    rw [← solRegistryStorage_array s i (by omega), hw.arrayWords i hi, targetAt_eq_getElem]

/-- A witness entry's stored pauser and index. -/
private theorem pauserOf_indexOf_getElem (hw : RegistryWitness (solRegistryStorage s) entries)
    {i : Nat} (h : i < entries.length) :
    pauserOf s (entries[i]'h).1 = (entries[i]'h).2 ∧
      indexOf s (entries[i]'h).1 = Nat.toB256 (i + 1) := by
  have hl1 := (l1_membership_raw hw (hw.targetsValid _ (List.getElem_mem h)).2).2.2 i _
    (findEntry_getElem entries hw.targetsNodup h)
  exact ⟨hl1.1, hl1.2.1⟩

/-- A Registry witness of the raw storage makes the stored Registry consistent. -/
theorem consistentRegistry_of_witness (hw : RegistryWitness (solRegistryStorage s) entries) :
    ConsistentRegistry s := by
  obtain ⟨hcount, hzero, -⟩ := l3_count_sum_raw hw
  rw [ConsistentRegistry, registeredTargets_eq hw]
  refine ⟨hw.targetsNodup, fun t ht => ⟨(l1_membership_raw hw ht).1,
    (l1_membership_raw hw ht).2.1⟩, fun i h => ?_, fun p hp => ?_, hzero⟩
  · rw [List.length_map] at h
    rw [List.getElem_map]
    exact (pauserOf_indexOf_getElem hw h).2
  · rw [guardCount, hcount p hp, assignmentCount_eq_count_map, List.count_eq_countP,
      List.countP_map, List.countP_map]
    congr 1
    apply List.countP_congr
    intro e he
    obtain ⟨i, h, rfl⟩ := List.getElem_of_mem he
    simp only [Function.comp_apply, (pauserOf_indexOf_getElem hw h).1, beq_iff_eq,
      decide_eq_true_eq]

/-- Witnesses of the storage before and after a removal of `t`, the second of the removed
entry list, together with `t`'s cleared pauser and index, give the repaired stored Registry. -/
theorem removalRepaired_of_witness {pre post : Stor} {t : B256}
    (hpre : RegistryWitness (solRegistryStorage pre) entries)
    (hpost : RegistryWitness (solRegistryStorage post) (removedEntries entries t))
    (hpauser : addressSlotReadWord (post.get (mapSlot t 3)) = 0)
    (hindex : post.get (mapSlot t 4) = 0) :
    RemovalRepaired pre post t := by
  refine ⟨hpauser, hindex, ?_⟩
  rw [registeredTargets_eq hpre, registeredTargets_eq hpost, removedEntries]
  cases hf : findEntry entries t with
  | none => simp only [findEntry_none_target_not_mem_targets hf, ↓reduceIte]
  | some found =>
      obtain ⟨index, pauser⟩ := found
      have hmem : t ∈ entries.map Prod.fst :=
        List.mem_map.mpr ⟨(t, pauser), mem_of_findEntry hf, rfl⟩
      simp only [hmem, ↓reduceIte, idxOf_of_findEntry hf, map_fst_swapPop]

end Blanc.Lift.LidoCircuitBreakerDeployed
