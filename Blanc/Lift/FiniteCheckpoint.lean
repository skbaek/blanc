import Blanc.SlotFootprint
import Blanc.Lift.LedgerFootprint
import Blanc.LadderBase

/-!
# A computable complete-support checker for slot footprints

`Blanc/SlotFootprint.lean` states a footprint over a set `K` of tracked keys: every nonzero storage
word sits at a fixed slot or at a tracked key's slot (`Support`), and the tracked slots are pairwise
distinct (`Inj`) and off the fixed slots (`Apart`).  This file decides those three facts for a
**finite row list** `rows : List (κ × B256)`, each row a key with its precomputed slot word, the
tracked set being the listed keys (`rowKeys rows`):

* `checkRows slot fixed rows s` checks, in one pass each: every row's word is its key's slot; the
  words are strictly ascending (so distinct, compared adjacent-wise, never pairwise); no word is a
  fixed slot; and every nonzero entry of the storage tree `s` (a `Std.TreeMap`, walked through its
  actual `toList`) is a fixed slot or a listed word (`covered`, a merge walk against the ascending
  words).  Its soundness is `checkRows_sound`.
* `checkSumNof w` decides `SumNof w.bal` by summing the balances of the world's actual accounts
  (`sum_bal_eq_worldBalSum`), since an address outside the tree reads the empty account.

Cost: with `n` rows and `m` storage entries, `checkRows` computes `n` slot words, makes `O(n)`
comparisons for ascent and apartness (`fixed` is a constant list), and walks the storage in
`O(n + m)`; `checkSumNof` is linear in the world's accounts plus one `O(log)` lookup each.  Soundness
does not depend on either list being sorted: an unsorted input only makes the walk answer `false`.

Nothing here names a contract.
-/

namespace Blanc.Lift.FiniteCheckpoint

open Jaune Blanc

/-! ## Strictly ascending words -/

/-- The words are strictly ascending, compared adjacent-wise. -/
def ascending : List B256 → Bool
  | a :: b :: t => decide (a < b) && ascending (b :: t)
  | _ => true

theorem ascending_pairwise : ∀ {l : List B256}, ascending l = true →
    l.Pairwise (fun a b => a.toNat < b.toNat)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    have tail := ascending_pairwise h.2
    have hab : a.toNat < b.toNat := B256.lt_iff_toNat_lt_toNat.mp h.1
    refine List.Pairwise.cons ?_ tail
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact Nat.lt_trans hab (List.rel_of_pairwise_cons tail hc)

theorem ascending_nodup {l : List B256} (h : ascending l = true) : l.Nodup :=
  (ascending_pairwise h).imp fun {a b} (hlt : a.toNat < b.toNat) (heq : a = b) =>
    Nat.lt_irrefl _ (heq ▸ hlt)

/-! ## Complete support by a merge walk -/

/-- Drop the words below `x` from the front of an ascending list. -/
def dropBelow (x : B256) : List B256 → List B256
  | [] => []
  | r :: rs => if r < x then dropBelow x rs else r :: rs

theorem mem_of_mem_dropBelow {x y : B256} : ∀ {l : List B256}, y ∈ dropBelow x l → y ∈ l
  | [], h => h
  | r :: rs, h => by
    unfold dropBelow at h
    split at h
    · exact List.mem_cons_of_mem r (mem_of_mem_dropBelow h)
    · exact h

/-- Every nonzero entry is a fixed slot or one of `words`.  The walk consumes the entries in order
and drops the words below each entry: linear in both lists when both ascend. -/
def covered (fixed : List B256) : List B256 → List (B256 × B256) → Bool
  | _, [] => true
  | words, e :: es =>
    if e.2 = 0 ∨ e.1 ∈ fixed then covered fixed words es
    else match dropBelow e.1 words with
      | r :: rs => decide (r = e.1) && covered fixed (r :: rs) es
      | [] => false

theorem covered_sound {fixed : List B256} :
    ∀ {words : List B256} {entries : List (B256 × B256)}, covered fixed words entries = true →
      ∀ e ∈ entries, e.2 ≠ 0 → e.1 ∈ fixed ∨ e.1 ∈ words
  | _, [], _ => fun _ h => absurd h List.not_mem_nil
  | words, e :: es, h => by
    intro e' he' hne
    unfold covered at h
    split at h
    · rename_i skip
      rcases List.mem_cons.mp he' with rfl | he'
      · rcases skip with hz | hf
        · exact absurd hz hne
        · exact Or.inl hf
      · exact covered_sound h e' he' hne
    · split at h
      · rename_i r rs hdrop
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have sub : ∀ y, y ∈ r :: rs → y ∈ words := fun y hy =>
          mem_of_mem_dropBelow (hdrop ▸ hy)
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inr (sub _ (h.1 ▸ List.mem_cons_self))
        · rcases covered_sound h.2 e' he' hne with hf | hw
          · exact Or.inl hf
          · exact Or.inr (sub _ hw)
      · exact absurd h Bool.false_ne_true

/-- A nonzero storage word is an entry of the storage tree. -/
theorem mem_toList_of_get_ne_zero {s : Stor} {x : B256} (hx : s.get x ≠ 0) :
    (x, s.get x) ∈ s.toList := by
  rw [Stor.mem_toList_iff]
  rw [Stor.get_eq_getD_find?] at hx ⊢
  cases hfind : s.find? x with
  | none => rw [hfind] at hx; exact absurd rfl hx
  | some v => rfl

/-! ## Row lists -/

/-- The tracked keys of a row list: the listed keys. -/
def rowKeys {κ : Type} (rows : List (κ × B256)) : κ → Prop := fun k => k ∈ rows.map Prod.fst

variable {κ : Type}

/-- **The footprint checker.**  Every row's word is its key's slot, the words strictly ascend,
none is a fixed slot, and every nonzero entry of `s` is a fixed slot or a listed word. -/
def checkRows (slot : κ → B256) (fixed : List B256) (rows : List (κ × B256)) (s : Stor) : Bool :=
  rows.all (fun r => decide (slot r.1 = r.2)) && ascending (rows.map Prod.snd) &&
    rows.all (fun r => decide (r.2 ∉ fixed)) && covered fixed (rows.map Prod.snd) s.toList

/-- What `checkRows` establishes: the footprint over the listed keys, plus the row facts the
contract-side checkers reuse (each word is its key's slot; the listed keys are distinct). -/
structure RowsSound (slot : κ → B256) (fixed : List B256) (rows : List (κ × B256)) (s : Stor) :
    Prop where
  word : ∀ r ∈ rows, slot r.1 = r.2
  nodup : (rows.map Prod.fst).Nodup
  support : SlotFootprint.Support slot fixed (rowKeys rows) s
  inj : SlotFootprint.Inj slot (rowKeys rows)
  apart : SlotFootprint.Apart slot fixed (rowKeys rows)

theorem rows_words_eq {slot : κ → B256} {rows : List (κ × B256)}
    (word : ∀ r ∈ rows, slot r.1 = r.2) :
    rows.map Prod.snd = (rows.map Prod.fst).map slot := by
  rw [List.map_map]
  exact List.map_congr_left fun r hr => (word r hr).symm

/-- **Soundness of the footprint checker.** -/
theorem checkRows_sound {slot : κ → B256} {fixed : List B256} {rows : List (κ × B256)} {s : Stor}
    (h : checkRows slot fixed rows s = true) : RowsSound slot fixed rows s := by
  simp only [checkRows, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨word, asc⟩, off⟩, cov⟩ := h
  have nodupWords := ascending_nodup asc
  rw [rows_words_eq word] at nodupWords
  refine ⟨word, nodupWords.of_map _, ?_, ?_, ?_⟩
  · intro x hx
    rcases covered_sound cov _ (mem_toList_of_get_ne_zero hx) hx with hf | hw
    · exact Or.inl hf
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
      exact Or.inr ⟨r.1, List.mem_map_of_mem hr, word r hr⟩
  · intro k k' hk hk' he
    exact List.inj_on_of_nodup_map nodupWords hk hk' he
  · intro k hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
    rw [word r hr]
    exact off r hr

/-! ## Account balances of a finite world -/

/-- The balances of the world's actual accounts, summed. -/
def worldBalSum (w : Jaune.State) : Nat := footprintSum w.keys w.bal

/-- An address outside the world's tree holds no balance, so the account list covers the full
address sum. -/
theorem sum_bal_eq_worldBalSum (w : Jaune.State) : sum w.bal = worldBalSum w := by
  refine (footprintSum_eq_sum Std.TreeMap.nodup_keys ?_).symm
  intro a ha
  apply Std.TreeMap.mem_keys.mpr
  apply Classical.byContradiction
  intro hout
  apply ha
  change (w.getD a .nil).bal = 0
  rw [Std.TreeMap.getD_eq_fallback hout]
  rfl

/-- The world-sum checker. -/
def checkSumNof (w : Jaune.State) : Bool := decide (worldBalSum w < 2 ^ 256)

theorem checkSumNof_sound {w : Jaune.State} (h : checkSumNof w = true) : SumNof w.bal := by
  unfold SumNof
  rw [sum_bal_eq_worldBalSum]
  exact of_decide_eq_true h

end Blanc.Lift.FiniteCheckpoint
