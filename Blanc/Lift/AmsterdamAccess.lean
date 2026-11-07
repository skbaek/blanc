import Blanc.Lift.AmsterdamWalk

/-!
# The slots a frame reads and writes under Amsterdam

A frame's EIP-7928 record, from its steps: `SLOAD` records a read, and `SSTORE` records a read and an explicit write. Under
any rules with a block access list. `Access` states a run of steps' record as lists of the slots at the frame's own address,
and composes.
-/

namespace Blanc.Lift

open Jaune

/-- A run of steps from `d` to `d'` adds these reads and writes to the record, at the frame's own address, and no others. -/
structure Access (s : Sevm) (d d' : Devm) (reads writes : List B256) : Prop where
  read : ∀ x, x ∈ d'.meta.storageReads ↔ x ∈ d.meta.storageReads ∨ ∃ k ∈ reads, x = (s.currentTarget, k)
  write : ∀ x, x ∈ d'.world.storageWrites ↔ x ∈ d.world.storageWrites ∨ ∃ k ∈ writes, x = (s.currentTarget, k)

namespace Access

variable {s : Sevm} {d e f : Devm} {r1 r2 w1 w2 : List B256}

theorem refl (s : Sevm) (d : Devm) : Access s d d [] [] :=
  ⟨fun x => by simp only [List.not_mem_nil, false_and, exists_false, or_false],
    fun x => by simp only [List.not_mem_nil, false_and, exists_false, or_false]⟩

theorem trans (h : Access s d e r1 w1) (k : Access s e f r2 w2) : Access s d f (r1 ++ r2) (w1 ++ w2) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [k.read, h.read]
    simp only [List.mem_append, or_and_right, exists_or, or_assoc]
  · rw [k.write, h.write]
    simp only [List.mem_append, or_and_right, exists_or, or_assoc]

theorem of_meta_world (hr : e.meta.storageReads = d.meta.storageReads)
    (hw : e.world.storageWrites = d.world.storageWrites) : Access s d e [] [] :=
  ⟨fun x => by rw [hr]; simp only [List.not_mem_nil, false_and, exists_false, or_false],
    fun x => by rw [hw]; simp only [List.not_mem_nil, false_and, exists_false, or_false]⟩

theorem mem_insert_key (S : KeySet) (a : Adr) (k : B256) (x : Adr × B256) :
    x ∈ S.insert (a, k) ↔ x ∈ S ∨ x = (a, k) := by
  rw [Std.HashSet.mem_insert, beq_iff_eq]
  constructor
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.symm

/-- `SLOAD`. -/
theorem sload (hbal : s.benvStat.rules.bal.isSome = true) (d : Devm) (k : B256) :
    Access s d (afterSloadA s d k) [k] [] := by
  have hbase : (afterSload s d k).meta.storageReads = d.meta.storageReads ∧
      (afterSload s d k).world.storageWrites = d.world.storageWrites := by
    unfold afterSload
    split <;> exact ⟨rfl, rfl⟩
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show x ∈ (Devm.balReadStorage _ _ _ (afterSload s d k)).meta.storageReads ↔ _
    unfold Devm.balReadStorage
    simp only [hbal, ↓reduceIte]
    show x ∈ (afterSload s d k).meta.storageReads.insert _ ↔ _
    rw [mem_insert_key, hbase.1]
    simp only [List.mem_singleton, exists_eq_left]
  · show x ∈ (afterSload s d k).world.storageWrites ↔ _
    rw [hbase.2]
    simp only [List.not_mem_nil, false_and, exists_false, or_false]

/-- `SSTORE`: a read and an explicit write of the slot. -/
theorem sstore (hbal : s.benvStat.rules.bal.isSome = true) (state : StateGasRules) (d : Devm) (k v : B256) :
    Access s d (afterSstoreA state s d k v) [k] [k] := by
  have hacc : ∀ c : Prop, ∀ [Decidable c], (if c then addAccessedStorageKey d s.currentTarget k else d).meta.storageReads =
      d.meta.storageReads ∧
      (if c then addAccessedStorageKey d s.currentTarget k else d).world.storageWrites = d.world.storageWrites := by
    intro c _
    split <;> exact ⟨rfl, rfl⟩
  have h := hacc (isColdA s d k)
  refine ⟨fun x => ?_, fun x => ?_⟩
  · unfold afterSstoreA Devm.balReadAccount Devm.balReadStorage
    simp only [hbal, ↓reduceIte]
    show x ∈ (if isColdA s d k then addAccessedStorageKey d s.currentTarget k else d).meta.storageReads.insert _ ↔ _
    rw [mem_insert_key, h.1]
    simp only [List.mem_singleton, exists_eq_left]
  · have hw : (afterSstoreA state s d k v).world.storageWrites =
        ((if isColdA s d k then addAccessedStorageKey d s.currentTarget k else d).world.storageWrites).insert
          (s.currentTarget, k) := rfl
    rw [hw, mem_insert_key, h.2]
    simp only [List.mem_singleton, exists_eq_left]

/-- The same record under the same lists, written differently. -/
theorem congr {r r' w w' : List B256} (h : Access s d e r w) (hr : ∀ k, k ∈ r ↔ k ∈ r') (hw : ∀ k, k ∈ w ↔ k ∈ w') :
    Access s d e r' w' := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [h.read]
    simp only [hr]
  · rw [h.write]
    simp only [hw]

/-- A list of `SLOAD`s. -/
theorem reads (hbal : s.benvStat.rules.bal.isSome = true) (keys : List B256) (d : Devm) :
    Access s d (readsBase s d keys) keys [] := by
  induction keys generalizing d with
  | nil => exact refl s d
  | cons k rest ih =>
    exact (((sload hbal d k).trans (ih (afterSloadA s d k))).congr (fun _ => Iff.rfl)
      (fun _ => Iff.rfl))

/-- A replacement of the machine registers records nothing. -/
theorem st (s : Sevm) (d : Devm) (S : List B256) (M : Mem) (G : Nat) : Access s d (St d S M G) [] [] :=
  of_meta_world rfl rfl

/-- A log records nothing. -/
theorem addLog (s : Sevm) (d : Devm) (l : Log) : Access s d (d.addLog l) [] [] :=
  of_meta_world rfl rfl

end Access

end Blanc.Lift
