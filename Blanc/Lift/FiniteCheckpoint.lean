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

/-! ## Complete support by a merge walk -/

/-- Drop the words below `x` from the front of an ascending list. -/
def dropBelow (x : B256) : List B256 → List B256
  | [] => []
  | r :: rs => if r < x then dropBelow x rs else r :: rs

/-- Every nonzero entry is a fixed slot or one of `words`.  The walk consumes the entries in order
and drops the words below each entry: linear in both lists when both ascend. -/
def covered (fixed : List B256) : List B256 → List (B256 × B256) → Bool
  | _, [] => true
  | words, e :: es =>
    if e.2 = 0 ∨ e.1 ∈ fixed then covered fixed words es
    else match dropBelow e.1 words with
      | r :: rs => decide (r = e.1) && covered fixed (r :: rs) es
      | [] => false

/-! ## Row lists -/

/-- The tracked keys of a row list: the listed keys. -/
def rowKeys {κ : Type} (rows : List (κ × B256)) : κ → Prop := fun k => k ∈ rows.map Prod.fst

variable {κ : Type}

/-- **The footprint checker.**  Every row's word is its key's slot, the words strictly ascend,
none is a fixed slot, and every nonzero entry of `s` is a fixed slot or a listed word. -/
def checkRows (slot : κ → B256) (fixed : List B256) (rows : List (κ × B256)) (s : Stor) : Bool :=
  rows.all (fun r => decide (slot r.1 = r.2)) && ascending (rows.map Prod.snd) &&
    rows.all (fun r => decide (r.2 ∉ fixed)) && covered fixed (rows.map Prod.snd) s.toList

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
